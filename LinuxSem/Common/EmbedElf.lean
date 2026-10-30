/-
  * Common/EmbedElf — elaborate a `MemImage` from an ELF at elaboration time

  `embedElf% "prog.elf"` parses a compiled riscv64 ELF and
  elaborates to a `MemImageType.MemImage` whose `loaded_segments`,
  `init_pc` and `phdrs` are the ones the kernel would set up for that file.
  A module can then be one line per binary:

      def SourceMemImage_image : MemImage := embedElf% "program.src.elf"

  and the C/Zig → ELF → Lean → proof pipeline has **no generated Lean file and
  no extracted payload** in it: the ELF is the artifact, and the image is read
  from it when the module is elaborated.  `Examples/RwxFlagNs` is the worked
  example: its two `MemImage` modules are one `embedElf%` each, and the proof
  is stated over them.

  ** What is checked, and where

  Everything `Common/ElfImage` refuses (`elf_load`'s page rounding and FILE
  mapping, the AT_PHDR derivation, non-overlap, congruent offsets, the
  page-rounded ceiling, the entry inside an executable segment, the phdr
  range readable) is checked HERE, at elaboration: a binary the model cannot
  faithfully run is a build failure, not an image with a caveat.  The
  page-rounded, `.bss`-zero-filled payload is cut into 8-byte hex chunks at
  elaboration, so the term in the `.olean` is a literal
  `List String` and every downstream `decide` indexes it.

  The build log gets the table for free, e.g.

      embedElf% program.src.elf: entry 0x10078, AT_PHDR 0x10040
        load 0x10000 + 0x1000 (rwx): file 0x0 + 0xe5, p_memsz 0xf0

  which is the readable part a generated snapshot module used to carry.

  This is elaboration-time IO, so Lean's build graph does not see the ELF: a
  binary replaced on its own does not invalidate the module that embedded it
  (`include_str` has the same caveat; `input_file` + `extraDepTargets` only
  order the target, they do not invalidate modules).  Replacing a committed
  binary by hand therefore needs the module's artifacts removed first —
  `Examples/RwxFlagNs/README.md` has the exact `rm` line — and the modules'
  own `decide` checks (layout, entry/phdr record, entry words) fail on a
  binary that is not the one the proof is written against, as soon as the
  module is actually rebuilt.
-/
import Lean
import LinuxSem.Common.ElfImage
import LinuxSem.LinuxProcessSem.MemImageType

set_option autoImplicit false

open Lean Elab Term

namespace LinuxSem.Common.EmbedElf

open LinuxSem.Common.ElfImage
open LinuxSem.LinuxProcessSem.MemImageType

syntax (name := embedElfSyntax) "embedElf% " term : term

/-- The `List String` LITERAL SYNTAX for `chunks` (spliceable into another
    quotation, which is what `Common/EmbedElf` needs for a whole `MemImage`). -/
def chunkListSyntax (chunks : List String) : TermElabM (TSyntax `term) := do
  let stxs ← chunks.toArray.mapM (fun c => `(term| $(Syntax.mkStrLit c)))
  `([$[$stxs],*])

/-- `embedElf% "file"` — the `MemImage` of a compiled riscv64 ELF, parsed and
    checked at elaboration.  The path resolves relative to the directory of
    the Lean file, like `include_str`. -/
@[term_elab embedElfSyntax] def elabEmbedElf : TermElab := fun stx expectedType? => do
  match stx with
  | `(embedElf% $path:term) => do
    let some rel := path.raw.isStrLit?
      | throwError "embedElf%: expected a string literal path, got{indentD path}"
    let ctx ← readThe Lean.Core.Context
    -- like `include_str`, but a file in the working directory (no parent
    -- component) resolves against `.` instead of failing
    let srcDir := (System.FilePath.mk ctx.fileName).parent.getD "."
    let bs ← IO.FS.readBinFile (srcDir / rel)
    let (e, segs, pa) ← match parseImage bs with
      | .ok r => pure r
      | .error msg => throwError "embedElf% {rel}: {msg}"
    -- report what was embedded (the generated module's table, in the log)
    logInfo m!"embedElf% {rel}: entry {hexLit e.entry}, AT_PHDR {hexLit pa}"
    for s in segs do
      logInfo m!"  load {hexLit s.base} + {hexLit s.size} ({s.perms}): \
file {hexLit s.raw.offset} + {hexLit s.raw.filesz}, p_memsz {hexLit s.raw.memsz}"
    let segTerms ← segs.mapM (fun s => do
      let chunks ← chunkListSyntax (segChunks s)
      let base := Syntax.mkNumLit (toString s.base)
      let size := Syntax.mkNumLit (toString s.size)
      `(term| ({ seg_base := $base, seg_size := $size,
                 seg_perms := $(Syntax.mkStrLit s.perms),
                 seg_bytes := $chunks } : Segment)))
    let segList ← `([$[$segTerms.toArray],*])
    let entry := Syntax.mkNumLit (toString e.entry)
    let addr := Syntax.mkNumLit (toString pa)
    let ent := Syntax.mkNumLit (toString e.phentsize)
    let num := Syntax.mkNumLit (toString e.phnum)
    elabTerm (← `(term| ({ loaded_segments := $segList, init_pc := $entry,
                           phdrs := ⟨$addr, $ent, $num⟩ } : MemImage))) expectedType?
  | _ => throwUnsupportedSyntax

end LinuxSem.Common.EmbedElf
