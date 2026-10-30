/-
  * Examples.RwxFlagNs.TargetMemImage — the TARGET binary, embedded from its ELF

  The committed artifact is the BINARY: `program.tgt.elf`, read at elaboration
  time by `embedElf%`.  As for the
  source, nothing is transcribed: the three segments, the entry and the
  program-header record come from the file, with `elf_load`'s page rounding,
  FILE-mapping bytes and AT_PHDR derivation applied.

  The image is the ordinary lld layout — THREE LOAD segments, no page both
  writable and executable:

  - `0x1000000`, `r--`, 4 KiB — ELF headers and the program header table
    (`0x1000040`, six entries);
  - `0x1001000`, `r-x`, 4 KiB — `.text`: six instructions, entry
    `0x1001190`;
  - `0x1002000`, `rw-`, 4 KiB — `.data`: the writable `flag` byte at
    `0x10021a8`.

  So this side of the pair is the standard static-fetch machinery — the
  `x /\ ~w` gate of `RiscvSemantics.code_read` accepts `.text`, and the
  overlay is never consulted for a fetch.

  ** Where the committed ELF comes from

  Same as the source (read `SourceMemImage.lean`'s note): the upstream
  repository ships the page images, and `program.tgt.elf` here is the
  loader-visible first page of the upstream Zig binary written back out as a
  file.  The whole binary is under one page (its section header table ends at
  `0x398`), so every byte any segment maps is present.

  A note on the three page images being identical: each segment's file extent
  (`p_offset` + `p_filesz` = `0x190`, `0x1a8`, `0x1a9`) is inside the first
  file page, and each page-rounded extent starts at its own `p_vaddr` page
  boundary, so `elf_load` maps the SAME file page into all three segments —
  at page offsets `0x190` (`.text`) and `0x1a8` (`flag`) for the last two.
  The bytes beyond each segment's own `p_filesz` extent are page fill the
  program never reads.
-/
import LinuxSem.Common.EmbedElf

/- The byte-level checks at the end go through the model's own hex
   decoder. -/
import LinuxSem.LinuxProcessSem.RiscvSemantics

set_option autoImplicit false
set_option maxRecDepth 40000

namespace LinuxSem.Examples.RwxFlagNs

namespace TargetMemImage

open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics

/-- The image, parsed from the committed ELF at elaboration. -/
def TargetMemImage_image : MemImage := embedElf% "program.tgt.elf"

/-- The `r--` header page. -/
def TargetMemImage_segment_000 : Segment :=
  TargetMemImage_image.loaded_segments.headD
    { seg_base := 0, seg_size := 0, seg_perms := "", seg_bytes := [] }

/-- The `r-x` `.text` page. -/
def TargetMemImage_segment_001 : Segment :=
  (TargetMemImage_image.loaded_segments.drop 1).headD
    { seg_base := 0, seg_size := 0, seg_perms := "", seg_bytes := [] }

/-- The `rw-` data page (the `flag` byte). -/
def TargetMemImage_segment_002 : Segment :=
  (TargetMemImage_image.loaded_segments.drop 2).headD
    { seg_base := 0, seg_size := 0, seg_perms := "", seg_bytes := [] }

def TargetMemImage_loaded_segments : List Segment :=
  TargetMemImage_image.loaded_segments

/-- `e_entry`: `_start` in `.text`. -/
def TargetMemImage_init_pc : Nat := TargetMemImage_image.init_pc

/-- `AT_PHDR`/`AT_PHENT`/`AT_PHNUM`, as the kernel publishes them. -/
def TargetMemImage_phdrs : PhdrInfo := TargetMemImage_image.phdrs

/-- The image packaged for the `Equivalence` functor as `Target: MemImage`. -/
def Target : MemImage := TargetMemImage_image

/-! ## Sanity checks

  As for the source: the ELF this module is stated over is pinned here — the
  three-segment shape, the entry/phdr record, and the bytes the fetch and
  store facts read. -/

example : TargetMemImage_image.loaded_segments.length = 3 := by decide

example : TargetMemImage_init_pc = 0x1001190 := by decide

example : TargetMemImage_phdrs = ⟨0x1000040, 56, 6⟩ := by decide

/-! ## Sanity checks

  The bytes are generated, so nothing but these checks pins them.
  They pin the layout
    the target derivation relies on: exactly one executable segment and it
    is NOT writable (so the static fetch path is the live one), the one
    writable segment is not executable, the entry point is in the `r-x`
    page, and the bytes at the entry point are the six instructions the
    derivation's generated facts claim. -/

example : seg_readable TargetMemImage_segment_000 = true := by decide

example : seg_writable TargetMemImage_segment_000 = false := by decide

example : seg_executable TargetMemImage_segment_000 = false := by decide

/-- The code page: executable, not writable.  This is the `x /\ ~w` gate's
    precondition, i.e. `no_ro_exec` is FALSE here and `fetch_word` — not
    the overlay path — is what runs. -/
example : seg_executable TargetMemImage_segment_001 = true := by decide

example : seg_writable TargetMemImage_segment_001 = false := by decide

example : seg_readable TargetMemImage_segment_001 = true := by decide

/-- The data page: writable, not executable. -/
example : seg_writable TargetMemImage_segment_002 = true := by decide

example : seg_executable TargetMemImage_segment_002 = false := by decide

/-- The entry point lies inside the `r-x` segment. -/
example : TargetMemImage_segment_001.seg_base ≤ TargetMemImage_init_pc
    ∧ TargetMemImage_init_pc + 4 ≤ TargetMemImage_segment_001.seg_base
        + TargetMemImage_segment_001.seg_size := by decide

/-- `_start`'s six instruction words, as the payload spells them
    little-endian at page offset `0x190`:

      lui a0, 0x1002 / addi a1, x0, 5 / sb a1, 424(a0) /
      lbu a0, 424(a0) / addi a7, x0, 93 / ecall. -/
example : segment_read_bytes TargetMemImage_segment_001.seg_bytes 0x190 24
    = some [0x37, 0x25, 0x00, 0x01,
            0x93, 0x05, 0x50, 0x00,
            0x23, 0x04, 0xb5, 0x1a,
            0x03, 0x45, 0x85, 0x1a,
            0x93, 0x08, 0xd0, 0x05,
            0x73, 0x00, 0x00, 0x00] := by decide

/-- The `flag` byte's initial value, 7, at the address the code stores to
    — inside the writable segment. -/
example : segment_byte_at TargetMemImage_segment_002.seg_bytes 0x1a8
    = some 0x07 := by decide

/-- `e_phnum = 6`, and the executable segment's (`ph[2]`) program header
    says `p_vaddr = 0x1001190` — the entry point. -/
example : segment_read_bytes TargetMemImage_segment_000.seg_bytes 0x38 2
    = some [0x06, 0x00] := by decide

example : segment_read_bytes TargetMemImage_segment_000.seg_bytes 0xc0 8
    = some [0x90, 0x11, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00] := by decide

/-- The chunk counts, so this tree note's "8-byte chunks" claim cannot
    drift: each payload is 4096 / 8 chunks. -/
example : TargetMemImage_segment_000.seg_bytes.length = 512 := by decide

example : TargetMemImage_segment_001.seg_bytes.length = 512 := by decide

example : TargetMemImage_segment_002.seg_bytes.length = 512 := by decide

end TargetMemImage

end LinuxSem.Examples.RwxFlagNs
