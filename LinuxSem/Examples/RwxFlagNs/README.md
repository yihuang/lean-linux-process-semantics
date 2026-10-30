# RwxFlagNs — provenance of the two snapshots

This directory holds the tree's flagship **compiled** example: a C source and a
Zig target with observable behavior proved equal (`Proof.lean`, via
`CatSim.cat_omni_strong_equiv_te`).  The programs themselves are restored from
the upstream repository (`rocq-linux-process-semantics`), which builds every
example from source:

| file | contents |
| --- | --- |
| `source/program.c` | the SOURCE program (C) |
| `source/rwx.lds`, `source/ldflags.txt` | the one-RWX-segment link, and the extra linker flags |
| `target/program.zig` | the TARGET program (Zig) |
| `target/flags.txt` | its extra compiler flags |
| `program.src.elf`, `program.tgt.elf` | the committed BINARIES the proofs are stated over: `SourceMemImage.lean` / `TargetMemImage.lean` are one-line `embedElf%` embeddings of them (`Common/EmbedElf` → `Common/ElfImage`), so the ELF is the artifact and no image is transcribed into Lean |
| `SourceMemImage.lean`, `TargetMemImage.lean` | the `MemImage` definitions (`embedElf%` + the names the proofs use) and the `decide` sanity checks that pin the ELF, its layout, its entry/phdr record and the payload bytes |

The C source needs the minimal start code and the two project-wide niceties in
[`../crt/`](../crt/):

* `_start.S` — the `-ns` ("no start files") entry: set up `gp`, publish
  `environ`, call `main`, exit with its return value.  No libc startup.
* `environ.S` — an 8-byte `.bss` slot for `environ`, used **only** by the
  `zig cc` fallback below.  Upstream gets that symbol from musl's libc; see
  the note in the file.

The binaries are not in the upstream repository (it ships the page images as
`.hex`), so `program.*.elf` are the loader-visible first pages of the upstream
builds written back out as files.  Each binary's ELF header, program header
table, every LOAD byte and its section header table lie inside that page (the
source's table ends at `0x528`, the target's at `0x398`), so the reconstruction
is exact for everything the kernel — and this model — reads; the page image
re-derived from it is byte-identical to the upstream `.hex` (that is how it was
checked).

## Rebuilding, and what "reproduced" means

```sh
bash tools/e2e/rwx_flag_ns.sh                # build both, compare at loader level
bash tools/e2e/rwx_flag_ns.sh --strict-bytes  # fail on any byte difference
```

The script uses the upstream command lines:

```sh
# source (in source/)
riscv64-linux-musl-gcc -std=gnu17 -march=rv64imafd -Os -static -nostartfiles \
  -fno-builtin -fno-strict-aliasing $(grep -hv '^#' ldflags.txt) \
  ../../crt/_start.S program.c -o program

# target
zig build-exe target/program.zig $(grep -hv '^#' target/flags.txt) \
  -target riscv64-linux-none -femit-bin=target/program
```

then compares each rebuilt file with its committed counterpart **as an ELF, at
the loader level** (`tools/e2e/compare_elfs.py`): the page-rounded segment
extents and permissions, the entry point, `e_phnum`/`e_phentsize` and the
AT_PHDR the kernel derives, then the bytes — per PT_LOAD the page image and the
segment's own **file extent** (`[p_vaddr, p_vaddr + p_filesz)`), i.e. the
program's own bytes separately from the page slack the kernel maps around them.

Measured on the machine this port was made on (zig 0.14.1; no
`riscv64-linux-musl-gcc`, so the source used the `zig cc` fallback):

| image | layout | program's own bytes |
| --- | --- | --- |
| target (Zig) | reproduced exactly | the `.text` extent `[0x1001190, 0x10011a8)` and the data byte `[0x10021a8, 0x10021a9)` are **byte-identical**; the only differing byte inside any LOAD file extent is `0x1000028`, the first byte of `e_shoff` (the section-header table pointer — a zig-version difference, and the section table itself is page slack this program never reads) |
| source (C) | reproduced exactly | 62 bytes differ across `[0x10028, 0x100e8]`: the fallback compiler is clang, the committed snapshot is the GNU build.  Install `riscv64-linux-musl-gcc` to reproduce it; that is the toolchain the snapshot is pinned to |

So the committed target snapshot is the current compiler's output up to the
ELF section table, and the committed source snapshot is the upstream GNU
build.  The proofs are stated over the committed bytes — a compiler upgrade
that changes them is a change to the example, not a silent re-baseline.

One caveat about the ELF files: `embedElf%` reads them at elaboration time, and
Lean's build does NOT track that read (neither does `include_str`).  Replacing a
binary by hand will not invalidate the module — the build keeps using the image
it parsed last time.  After replacing one, delete the module's artifacts first:

```sh
rm -f .lake/build/lib/lean/LinuxSem/Examples/RwxFlagNs/{Source,Target}MemImage.{olean,olean.hash,ilean,ilean.hash,trace}
```

and rebuild; the modules' `decide` sanity checks then fail if the new binary is
not the one the proof is written against.

The script never overwrites the committed binaries: it builds into `.lake/e2e/rwx/`
and compares.  Re-baselining an image means copying a rebuilt binary over
`program.*.elf` and re-checking the proof — the script's per-segment report says
exactly which bytes moved, and the modules' `decide` checks fail if the ELF's
layout, entry, phdr record or entry bytes are not the ones the proof expects.

## Why the image is page-rounded

The source image's segment is `0x10000 + 0x1000` even though the ELF's
`p_memsz` is `0xf0`.  That is not padding for convenience: the kernel maps
whole pages (`Run.segment_reservation` reserves exactly those), and the pages
are a **file** mapping, so the bytes around the segment come from the file —
the ELF header and program header table before `p_vaddr`, and (for a
`p_memsz == p_filesz` segment) whatever file bytes follow it inside the last
page.  `Common/ElfImage` implements `elf_load`'s computation, which is why the
embedded image needs no post-processing.
