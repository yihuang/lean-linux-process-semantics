/-
  * Examples.RwxFlagNs.SourceMemImage — the SOURCE binary, embedded from its ELF

  The committed artifact is the BINARY: `program.src.elf`, read at elaboration
  time by `embedElf%`.  Nothing is transcribed into Lean:
  the segment, the entry and the program-header record all come from the file,
  with `elf_load`'s page rounding, FILE-mapping bytes and AT_PHDR derivation
  applied and every refusal (`Common/ElfImage`'s header) enforced.

  ** What the binary is

  ONE LOAD segment, `rwx`, at `0x10000`, page-rounded to 4 KiB: the ELF
  headers, `.text` and the writable data all share it (built through
  `source/rwx.lds`, which is why the example exists).  Inside the segment,

  - `0x000 .. 0x078`  ELF header, program header table, and `_start`'s
    opening `auipc gp, 0x1` is at `0x078` itself;
  - `0x078 .. 0x0e4`  `.text` — the eighteen instructions the source
    derivation steps through.  This is the range `stext_lo`/`stext_hi`
    in `RwxFlagNsDefs.lean` states the `mem_clear` frame invariant over;
  - `0x0e4 .. 0x1000` `.data`/`.bss` — the `flag` byte at `0x100e4` (its
    initial value 7), musl's `__environ` slot at `0x100e8` — then the
    page's zero fill.

  ** Where the committed ELF comes from

  The upstream snapshot is a GNU riscv64-linux-musl-gcc build, and the
  upstream repository ships the PAGE IMAGES (`.hex`), not the binary.  So
  `program.src.elf` here is the loader-visible first page of that binary,
  written back out as a file: the ELF header, the program header table, every
  LOAD byte and the section header table all lie inside that page (it ends at
  `0x528`), so the reconstruction is exact for everything the kernel reads —
  and `embedElf%` reproduces the committed page image byte for byte
  (`tools/e2e/rwx_flag_ns.sh` compares a rebuilt binary against this file at
  the loader level).

  The sanity checks at the end pin the pieces of that image the proof's fetch
  facts read, and the layout facts the example is about: one `rwx` segment, at
  `0x10000`, 4 KiB, entry `0x10078`, one phdr entry at `0x10040`.
-/
import LinuxSem.Common.EmbedElf

/- The byte-level checks at the end go through the model's own hex
   decoder (`segment_read_bytes`). -/
import LinuxSem.LinuxProcessSem.RiscvSemantics

/- `autoImplicit` is off: a bare field name in a statement would otherwise
   become an implicitly bound variable, i.e. a weakened claim rather than a
   compile error. -/
set_option autoImplicit false

/- The byte-level checks reduce the model's hex decoder; that is deeper than
   the default `decide` recursion budget.  A resource knob, not a proof step. -/
set_option maxRecDepth 40000

namespace LinuxSem.Examples.RwxFlagNs

namespace SourceMemImage

open LinuxSem.LinuxProcessSem.MemImageType
open LinuxSem.LinuxProcessSem.RiscvSemantics

/-- The image, parsed from the committed ELF at elaboration.  The build log
    shows what was embedded:
    `entry 0x10078, AT_PHDR 0x10040; load 0x10000 + 0x1000 (rwx)`. -/
def SourceMemImage_image : MemImage := embedElf% "program.src.elf"

/-- The image's single LOAD segment: the whole binary, RWX.  This layout
    is what the example is ABOUT — an ordinary GNU-ld
    `-z noseparate-code` merge — so every instruction fetch has to go
    through the overlay-aware w+x path (`RiscvSemantics.code_read_ov`). -/
def SourceMemImage_segment_000 : Segment :=
  SourceMemImage_image.loaded_segments.headD
    { seg_base := 0, seg_size := 0, seg_perms := "", seg_bytes := [] }

def SourceMemImage_loaded_segments : List Segment :=
  SourceMemImage_image.loaded_segments

/-- `e_entry`: `_start`, inside the RWX segment. -/
def SourceMemImage_init_pc : Nat := SourceMemImage_image.init_pc

/-- `AT_PHDR`/`AT_PHENT`/`AT_PHNUM` as the kernel publishes them: the
    table lies inside the same RWX segment (`e_phoff = 0x40`, one entry). -/
def SourceMemImage_phdrs : PhdrInfo := SourceMemImage_image.phdrs

/-- The image packaged for the `Equivalence` functor as `Source: MemImage`.
  Lean has no module types, so the three parameters are the three fields
  of the `MemImage` structure (see `MemImageType.lean`). -/
def Source : MemImage := SourceMemImage_image

/-! ## Sanity checks

  These pin the ELF the module is stated over: the layout the demo's story
  turns on (one RWX segment, so the STATIC fetch declines and the
  overlay-aware one is the live path), the entry/phdr record, and the pieces
  of the payload the proof's fetch facts read.  A different binary fails
  here. -/

/-- The ELF really has the one-segment shape the example is about. -/
example : SourceMemImage_image.loaded_segments.length = 1 := by decide

example : SourceMemImage_init_pc = 0x10078 := by decide

example : SourceMemImage_phdrs = ⟨0x10040, 56, 1⟩ := by decide

/-! ## Sanity checks

  The bytes are generated, so nothing but these checks pins them.
  They pin the layout
    the demo's story turns on — the segment is RWX, so the STATIC fetch
    declines and the overlay-aware one is the live path — and, at the byte
    level, the pieces of the payload the proof's fetch facts will read.
    A transcription error in the 4 KiB above fails here. -/

example : seg_readable SourceMemImage_segment_000 = true := by decide

example : seg_writable SourceMemImage_segment_000 = true := by decide

example : seg_executable SourceMemImage_segment_000 = true := by decide

/-- The entry point lies inside the segment. -/
example : SourceMemImage_segment_000.seg_base ≤ SourceMemImage_init_pc
    ∧ SourceMemImage_init_pc + 4 ≤ SourceMemImage_segment_000.seg_base
        + SourceMemImage_segment_000.seg_size := by decide

/-- The ELF magic, through the model's own byte decoder. -/
example : segment_read_bytes SourceMemImage_segment_000.seg_bytes 0 4
    = some [0x7f, 0x45, 0x4c, 0x46] := by decide

/-- `e_entry` as the ELF header holds it, little-endian at offset `0x18`:
    `0x10078`. -/
example : segment_read_bytes SourceMemImage_segment_000.seg_bytes 0x18 8
    = some [0x78, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00] := by decide

/-- `e_phoff = 0x40`, `e_phentsize = 56`, `e_phnum = 1` — the values
    `SourceMemImage_phdrs` publishes. -/
example : segment_read_bytes SourceMemImage_segment_000.seg_bytes 0x20 8
    = some [0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] := by decide

example : segment_read_bytes SourceMemImage_segment_000.seg_bytes 0x36 2
    = some [0x38, 0x00] := by decide

example : segment_read_bytes SourceMemImage_segment_000.seg_bytes 0x38 2
    = some [0x01, 0x00] := by decide

/-- The one program header is `PT_LOAD` with flags 7 (`rwx`) over the
    whole file — the merged layout, straight out of the payload. -/
example : segment_read_bytes SourceMemImage_segment_000.seg_bytes 0x40 4
    = some [0x01, 0x00, 0x00, 0x00] := by decide

example : segment_read_bytes SourceMemImage_segment_000.seg_bytes 0x44 4
    = some [0x07, 0x00, 0x00, 0x00] := by decide

/-- The last instruction of `_start`'s exit path, `ecall`, at `0x100a8`,
    and the first, `auipc gp, 0x1` at `0x10078` — the two ends of the
    range the derivation walks. -/
example : segment_read_bytes SourceMemImage_segment_000.seg_bytes 0xa8 4
    = some [0x73, 0x00, 0x00, 0x00] := by decide

example : segment_read_bytes SourceMemImage_segment_000.seg_bytes 0x78 4
    = some [0x97, 0x11, 0x00, 0x00] := by decide

/-- `flag` starts at 7 (`0x100e4`). -/
example : segment_byte_at SourceMemImage_segment_000.seg_bytes 0xe4
    = some 0x07 := by decide

/-- The chunk count, so the "8-byte chunks" claim in this tree note cannot
    drift: 4096 / 8. -/
example : SourceMemImage_segment_000.seg_bytes.length = 512 := by decide

end SourceMemImage

end LinuxSem.Examples.RwxFlagNs
