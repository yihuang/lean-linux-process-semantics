/-
  * Common/ElfImage — parse an ELF64 (riscv64) into the model's page image

  The pure half of the embedding pipeline: bytes in, the `Segment`s the kernel
  would map plus the program-header address it would publish, or the reason the
  file cannot be snapshotted.  No IO — `Common/EmbedElf`'s `embedElf% "file"`
  owns the read and elaborates the `MemImage` at elaboration time, so a module
  can say

      def SourceMemImage_image : MemImage := embedElf% "program.src.elf"

  and the source → ELF → Lean → proof pipeline has no generated file in it;

  ## Why the byte computation is not a dump

  `MemImageType.Segment` is the library's snapshot format, and two of its
  conventions come from the kernel, not from the ELF:

  1. **Page granularity.**  `Run.segment_reservation` reserves
     `[round_down(p_vaddr), round_up(p_vaddr + p_memsz))`, which is what
     `elf_load` mmaps.  A snapshot therefore emits the segment at that
     page-rounded base and size, not at `p_vaddr`/`p_memsz` — otherwise
     `find_segment`/`wview` disagree with the real mapping about the slack.
     (The committed `Examples/RwxFlagNs` snapshots show it: a source binary
     with `p_memsz = 0xf8` is emitted as one 0x1000-byte segment.)
  2. **The pages are a FILE mapping.**  `elf_load` mmaps the pages
     `[round_down(p_vaddr), round_up(p_vaddr + p_filesz))` from the file, so
     the head slack before `p_vaddr` (for a layout whose first section starts
     mid-page: the ELF header and program header table) and the tail of the
     last file page hold REAL FILE BYTES, not zeros.  Only a segment with
     `p_memsz > p_filesz` is zeroed past `p_vaddr + p_filesz` (the rest of that
     page plus the remaining pages are anonymous).  Bytes past EOF read as
     zeros.  `Elf.segOf` reproduces exactly that.

  `PhdrInfo` is DERIVED: for the PT_LOAD whose FILE extent covers `e_phoff`,
  `p_vaddr + (e_phoff - p_offset)`; the kernel's loop has no `break`, so when
  several segments cover the table the LAST one in program-header order wins,
  and this parser reproduces that rather than taking the first.

  ## Refusals

  A file that cannot be snapshotted faithfully is rejected with the reason,
  never emitted with a guess: bad magic/class/encoding/machine; a truncated
  header or phdr table; a table over Linux's 64 KiB `load_elf_phdrs` limit;
  `p_filesz > p_memsz`; a segment whose file extent runs past EOF;
  `p_offset`/`p_vaddr` not congruent mod the page size (`elf_map` would fail
  the execve); a page-rounded extent above `0x1_00000000`; overlapping
  page-rounded extents (the kernel resolves overlaps last-mapping-wins while
  `find_segment` is first-match); no covering PT_LOAD for `e_phoff` (no
  AT_PHDR); a phdr range not wholly inside a readable snapshotted segment; and
  an entry point outside every executable segment or 2-byte misaligned.
-/
set_option autoImplicit false

namespace LinuxSem.Common.ElfImage


/-! ## Little-endian readers -/

def u8 (b : ByteArray) (o : Nat) : Nat := (b.get! o).toNat

def u16 (b : ByteArray) (o : Nat) : Nat :=
  u8 b o + u8 b (o + 1) * 0x100

def u32 (b : ByteArray) (o : Nat) : Nat :=
  u16 b o + u16 b (o + 2) * 0x10000

/-- 64-bit little-endian, kept in `Nat`: every field this tool consumes is an
    offset, an address or a size, all of which the model carries as `Nat`. -/
def u64 (b : ByteArray) (o : Nat) : Nat :=
  u32 b o + u32 b (o + 4) * 0x100000000

/-! ## Hex formatting -/

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

/-- Lowercase hex of `n`, zero-padded to `w` digits. -/
def hexNat (w : Nat) (n : Nat) : String :=
  let ds := Nat.toDigits 16 n
  let ds := List.replicate (w - ds.length) '0' ++ ds
  String.ofList ds

def hexByte (n : Nat) : String := hexNat 2 n

/-- A hexadecimal Lean literal (`0x…`), as the snapshot modules spell
    addresses and sizes. -/
def hexLit (n : Nat) : String := "0x" ++ hexNat 0 n

/-! ## Page arithmetic (the kernel's, not the ELF's) -/

def pageSize : Nat := 4096

/-- Hard ceiling on a page-rounded segment end: above it a loaded segment can
    collide with the syscall model's allocator grants. -/
def segEndCeiling : Nat := 0x100000000

/-- Linux refuses a program header table larger than 64 KiB
    (`load_elf_phdrs`, fs/binfmt_elf.c). -/
def phdrTableMax : Nat := 65536

def pageDown (x : Nat) : Nat := x / pageSize * pageSize
def pageUp (x : Nat) : Nat := (x + pageSize - 1) / pageSize * pageSize

/-! ## The ELF program header table -/

structure Phdr where
  /-- `p_type` (`1` = PT_LOAD). -/
  ptype : Nat
  /-- `p_flags`: PF_X = 1, PF_W = 2, PF_R = 4. -/
  flags : Nat
  /-- `p_offset` — file offset of the segment image. -/
  offset : Nat
  /-- `p_vaddr` — run-time base address. -/
  vaddr : Nat
  /-- `p_filesz` — bytes present in the file. -/
  filesz : Nat
  /-- `p_memsz` — bytes the segment occupies in memory. -/
  memsz : Nat
  deriving Repr, Inhabited

def Phdr.isLoad (p : Phdr) : Bool := p.ptype == 1

/-- The ELF permission rendering the model gates on: `"rwx"` with `'-'` for
    an unset bit.  `Segment.seg_perms` is scanned for its letters, so the
    spelling is the format, not a comment. -/
def Phdr.perms (p : Phdr) : String :=
  let b (bit : Nat) (c : Char) : Char := if p.flags / bit % 2 == 1 then c else '-'
  String.ofList [b 4 'r', b 2 'w', b 1 'x']

/-! ## A page-rounded segment, with the bytes the kernel would map -/

structure Seg where
  /-- `round_down(p_vaddr)` — `Segment.seg_base`. -/
  base : Nat
  /-- `round_up(p_vaddr + p_memsz) - base` — `Segment.seg_size`. -/
  size : Nat
  perms : String
  /-- The mapped bytes, `size` of them. -/
  data : List Nat
  /-- The raw program header, kept for the AT_PHDR computation. -/
  raw : Phdr
  deriving Inhabited

/-! ## Parsing -/

structure Elf where
  entry : Nat
  phoff : Nat
  phentsize : Nat
  phnum : Nat
  phdrs : List Phdr
  bytes : ByteArray
  deriving Inhabited

abbrev ParseM := Except String

def checkHeader (b : ByteArray) : ParseM Unit := do
  if b.size < 64 then throw "not an ELF file: shorter than the 64-byte header"
  if !(u8 b 0 == 0x7f && u8 b 1 == 0x45 && u8 b 2 == 0x4c && u8 b 3 == 0x46) then
    throw "not an ELF file: bad magic"
  if !(u8 b 4 == 2) then throw "not a 64-bit ELF (EI_CLASS ≠ 2)"
  if !(u8 b 5 == 1) then throw "not a little-endian ELF (EI_DATA ≠ 1)"
  if !(u16 b 18 == 243) then throw "not a riscv64 ELF (e_machine ≠ 243)"

def readPhdrs (b : ByteArray) (phoff entsize num : Nat) : ParseM (List Phdr) := do
  if entsize < 56 then throw s!"program header entry too small: e_phentsize = {entsize}"
  if num * entsize > phdrTableMax then
    throw s!"e_phnum = {num}: Linux's execve refuses a phdr table over 64 KiB"
  if phoff + num * entsize > b.size then
    throw "program header table lies outside the file"
  let mut ps : List Phdr := []
  for i in [0:num] do
    let o := phoff + i * entsize
    ps := ps ++ [{ ptype := u32 b o
                   flags := u32 b (o + 4)
                   offset := u64 b (o + 8)
                   vaddr := u64 b (o + 16)
                   filesz := u64 b (o + 32)
                   memsz := u64 b (o + 40) }]
  pure ps

def parse (b : ByteArray) : ParseM Elf := do
  checkHeader b
  let entry := u64 b 0x18
  let phoff := u64 b 0x20
  let phentsize := u16 b 0x36
  let phnum := u16 b 0x38
  let phdrs ← readPhdrs b phoff phentsize phnum
  pure { entry, phoff, phentsize, phnum, phdrs, bytes := b }

/-! ## From program headers to mapped pages -/

/-- `p_offset` and `p_vaddr` must be congruent mod the page size: the kernel's
    `elf_map` passes `vm_mmap` the file offset `p_offset - (p_vaddr % PAGE)`
    and refuses a non-page-aligned one, failing the execve outright. -/
def Phdr.congruent (p : Phdr) : Bool := p.offset % pageSize == p.vaddr % pageSize

/-- One PT_LOAD, page-rounded, with the byte computation `elf_load` makes:

    - the pages covering `[p_vaddr, p_vaddr + p_filesz)` come from the file at
      `p_offset - (p_vaddr - ext_lo)`;
    - if `p_memsz > p_filesz` everything past `p_vaddr + p_filesz` is zeroed;
    - bytes past EOF read as zeros. -/
def Elf.segOf (e : Elf) (p : Phdr) : ParseM Seg := do
  if p.filesz > p.memsz then throw "p_filesz > p_memsz"
  if p.offset + p.filesz > e.bytes.size then
    throw s!"PT_LOAD at {hexLit p.vaddr}: file extent runs past end of file"
  if !p.congruent then
    throw s!"PT_LOAD at {hexLit p.vaddr}: p_offset {hexLit p.offset} and \
p_vaddr are not congruent mod the 0x1000 page size; the kernel's elf_map \
would fail the execve"
  if pageUp (p.vaddr + p.memsz) > segEndCeiling then
    throw s!"PT_LOAD at {hexLit p.vaddr}: page-rounded extent reaches \
{hexLit (pageUp (p.vaddr + p.memsz))}, above the {hexLit segEndCeiling} ceiling"
  let extLo := pageDown p.vaddr
  let extHi := pageUp (p.vaddr + p.memsz)
  let extSize := extHi - extLo
  let delta := p.vaddr - extLo
  let data : List Nat :=
    if p.filesz == 0 then List.replicate extSize 0
    else
      -- congruent ⇒ `offset = delta + k*4096` for k ≥ 0, so this cannot
      -- underflow; a crafted negative would have been refused above.
      let fileLo := p.offset - delta
      let fileSpan := pageUp (delta + p.filesz)
      let raw := (List.range fileSpan).map
        (fun i => if fileLo + i < e.bytes.size then u8 e.bytes (fileLo + i) else 0)
      -- a bss-carrying segment is zeroed past p_vaddr + p_filesz
      let mapped := if p.memsz > p.filesz then raw.take (delta + p.filesz) else raw
      mapped ++ List.replicate (extSize - mapped.length) 0
  pure { base := extLo, size := extSize, perms := p.perms, data := data, raw := p }

/-- The mapped segments, in program-header order, with the checks that make an
    overlapping or unmappable image a refusal rather than a surprise. -/
def Elf.segments (e : Elf) : ParseM (List Seg) := do
  let mut segs : List Seg := []
  for p in e.phdrs do
    if p.isLoad && p.memsz > 0 then
      segs := segs ++ [← e.segOf p]
  if segs.isEmpty then throw "no mapped PT_LOAD segment"
  -- pairwise non-overlap of the page-rounded extents
  let sorted := segs.mergeSort (fun a b => a.base < b.base)
  let rec noOverlap : List Seg → ParseM Unit
    | [] => pure ()
    | [_] => pure ()
    | a :: b :: rest =>
      if a.base + a.size > b.base then
        throw s!"overlapping LOAD segments: [{hexLit a.base}, \
{hexLit (a.base + a.size)}) and [{hexLit b.base}, {hexLit (b.base + b.size)}); \
the kernel resolves overlaps last-mapping-wins while the model's find_segment \
scan is first-match"
      else noOverlap (b :: rest)
  noOverlap sorted
  pure segs

/-- Is `[a, a+n)` wholly inside one readable snapshotted segment? -/
def segsReadable (segs : List Seg) (a n : Nat) : Bool :=
  segs.any (fun s => s.perms.contains 'r' && a >= s.base && a + n <= s.base + s.size)

/-- AT_PHDR: for the PT_LOAD whose FILE extent covers `e_phoff`,
    `p_vaddr + (e_phoff - p_offset)`.  The kernel's loop has no `break`, so
    the LAST covering segment in program-header order wins; this scans in that
    order and keeps the last match.  Fails if no segment covers the table or
    the mapped range is not readable in the snapshot. -/
def Elf.phdrAddr (e : Elf) (segs : List Seg) : ParseM Nat := do
  let covering := segs.filter (fun s =>
    s.raw.offset <= e.phoff && e.phoff < s.raw.offset + s.raw.filesz)
  match covering.getLast? with
  | none =>
    throw s!"the phdr table at file offset {hexLit e.phoff} is not inside any \
PT_LOAD's file extent, so the kernel would publish no AT_PHDR"
  | some s =>
    let addr := s.raw.vaddr + (e.phoff - s.raw.offset)
    let n := e.phnum * e.phentsize
    if !(segsReadable segs addr n) then
      throw s!"the phdr table maps to [{hexLit addr}, {hexLit (addr + n)}), not \
wholly inside a readable snapshotted segment"
    pure addr

/-- The entry point must land in an executable, mapped segment and be 2-byte
    aligned (RV64 with the C extension has IALIGN = 16). -/
def Elf.checkEntry (e : Elf) (segs : List Seg) : ParseM Unit := do
  let some s := segs.find? (fun s => s.base <= e.entry && e.entry + 1 ≤ s.base + s.size)
    | throw s!"entry point {hexLit e.entry} is outside every mapped PT_LOAD"
  if !(s.perms.contains 'x') then
    throw s!"entry point {hexLit e.entry} lies in a non-executable segment ({s.perms})"
  if e.entry % 2 != 0 then
    throw s!"entry point {hexLit e.entry} is not 2-byte aligned"

/-! ## Emitting the module -/

/-- Four 8-byte chunks per source line, with the line's segment-relative
    offset in a comment. -/
def renderChunkLines (chunks : List String) : String :=
  let lines := (List.range ((chunks.length + 3) / 4)).map (fun i =>
    let line := (chunks.drop (i * 4)).take 4
    let offs := hexNat 3 (i * 32)
    let body := String.intercalate ", " (line.map (fun s => "\"" ++ s ++ "\""))
    s!"      -- 0x{offs}\n      {body},\n")
  "[\n" ++ String.join lines ++ "    ]"

/-- A stable 64-bit FNV-style digest of a payload, printed in the generated
    module's header.  It is not a security hash: its only job is to make the
    module SOURCE change when the payload changes, so Lake rebuilds the module
    (elaboration-time file reads are outside its dependency graph). -/
def payloadDigest (bytes : List Nat) : String :=
  let h := bytes.foldl (fun h b => (h * 1099511628211 + b + 14695981039346656037)
    % 18446744073709551616) 0
  hexNat 16 h

def segChunks (s : Seg) : List String :=
  (List.range ((s.data.length + 7) / 8)).map (fun i =>
    String.join (((s.data.drop (i * 8)).take 8).map hexByte))

def pad3 (n : Nat) : String := hexNat 3 n


/-- Parse a whole image: the ELF header data the `MemImage` needs, the mapped
    segments, and the AT_PHDR the kernel would publish — with every check above
    performed. -/
def parseImage (bs : ByteArray) : ParseM (Elf × List Seg × Nat) := do
  let e ← parse bs
  let segs ← e.segments
  e.checkEntry segs
  let pa ← e.phdrAddr segs
  pure (e, segs, pa)

end LinuxSem.Common.ElfImage
