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

The C source needs the minimal start code in [`../crt/`](../crt/):
`_start.S`, the `-ns` ("no start files") entry — set up `gp`, publish
`environ` (the symbol comes from musl's libc, which the link still pulls in),
call `main`, exit with its return value.  No libc startup.

The binaries are not in the upstream repository (it ships the page images as
`.hex`), so `program.*.elf` are the loader-visible first pages of the upstream
builds written back out as files.  Each binary's ELF header, program header
table, every LOAD byte and its section header table lie inside that page (the
source's table ends at `0x528`, the target's at `0x398`), so the reconstruction
is exact for everything the kernel — and this model — reads; the page image
re-derived from it is byte-identical to the upstream `.hex` (that is how it was
checked).

## Rebuilding, and what "reproduced" means

Both compilers are required — there is no fallback: `zig` for the target, and a
GNU `riscv64-linux-musl-gcc` for the source.  `shell.nix` at the repository root
puts the latter on `PATH` from nixpkgs:

```sh
nix-shell --run 'bash tools/e2e/rwx_flag_ns.sh'      # or: nix shell nixpkgs#pkgsCross.riscv64-musl.stdenv.cc -c …
```

On **aarch64-darwin** that means compiling GCC: the cross compiler is a host
tool and cache.nixos.org has no darwin builds, so `nix-shell` builds GCC
(15.2.0 on nixos-unstable) from source — tens of minutes.  Use a Linux host (CI
does), a Linux builder, or a prebuilt `riscv64-linux-musl` toolchain (musl.cc's
tarball, ~108 MB) with `SOURCE_CC=<prefix>/bin/riscv64-linux-musl-gcc`.

```sh
bash tools/e2e/rwx_flag_ns.sh                # build both, compare at loader level
bash tools/e2e/rwx_flag_ns.sh --strict-bytes  # fail on any byte difference
```

The script refuses to run without the GNU compiler rather than building the
source with a different one: the committed source binary is one specific GNU
musl build, and nixpkgs' cross GCC is whatever version the channel has.  A
different GCC version is expected to emit a different program (same layout);
that is the warning the source side prints, and the reason its *program* bytes
are not a hard gate.  With the compiler the binary was built with,
`--strict-bytes` is the exact gate.

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
the loader level** (`tools/e2e/compare_elfs.py`).  Three checks, in order:

1. **Layout** — the page-rounded segment extents and permissions, the entry
   point, `e_phnum`/`e_phentsize` and the AT_PHDR the kernel derives.  Required
   for both sides.
2. **Program bytes** — each PT_LOAD's own file extent
   (`[p_vaddr, p_vaddr + p_filesz)`), with the ELF header's section-table
   bookkeeping (`e_shoff`/`e_shentsize`/`e_shnum`/`e_shstrndx`) masked.  The
   section table is not loaded, not executed and never read by the program, and
   no two toolchains put it in the same place; the code and data a program runs
   on must not move.  Required for the **target** (its compiler family is
   pinned); the **source** side reports it but does not fail, for the
   compiler-version reason above.
3. **Page images** — only with `--strict-bytes`: the bytes the kernel maps,
   page slack included.  That is exact reproduction and needs the compiler the
   binary was built with.

`--allow-program-drift` drops check 2 (for trying a different toolchain).

### Re-baselining after a source change

```sh
bash tools/e2e/rwx_flag_ns.sh --update
```

writes the rebuilt binaries back over `program.src.elf` / `program.tgt.elf`,
but only for a side whose **program** changed — on a clean checkout it writes
nothing and leaves the committed binaries (and their upstream section tables)
alone.  Two guards:

- a **layout** change is refused (it changes the example's shape, which the
  proof's statements are written against) unless `--force` is given;
- the **source** binary is only replaced when `--update-source` is given: it is
  one specific GNU build, and a different compiler will emit a different program
  without that meaning the source changed.  `--update --update-source` is the
  explicit re-baseline, with the proof work it implies.

After writing, the script deletes the two image modules' build artifacts
(`embedElf%` reads the ELF at elaboration, outside Lake's dependency graph) and
prints the Lean command to run.  That build is the second half of the loop:
the modules' `decide` checks and then the derivation in
`RwxFlagNsSource.lean` / `RwxFlagNsTarget.lean` fail if the instruction stream
moved, so a re-baseline cannot silently outrun the proof.

Measured on the machine this port was made on (zig 0.14.1):

| image | layout | program bytes | script |
| --- | --- | --- | --- |
| target (Zig) | reproduced | **identical** after masking `e_shoff` (the only differing byte in any file extent is `0x1000028`, the first byte of that pointer); `.text [0x1001190, 0x10011a8)` and the data byte `[0x10021a8, 0x10021a9)` are byte-identical | exit 0 |
| source (C) | reproduced | depends on the GNU musl compiler version; the committed binary is one specific build.  With an exact match, `--strict-bytes` passes; otherwise the drift is reported and `--update --update-source` re-baselines | exit 0, WARN |

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

## CI

`.github/workflows/ci.yml` has two jobs, one per direction of the pipeline:

- **`build`** — `scripts/check.sh`.  RwxFlagNs is in the root module, so this
  runs `embedElf%` over the committed ELFs and typechecks the proof stated over
  those images (the binaries → Lean direction).
- **`e2e`** — installs nix (for nixpkgs' `riscv64-linux-musl-gcc`) and zig
  0.14.1 (pinned by checksum), then runs `tools/e2e/rwx_flag_ns.sh` under
  `nix shell nixpkgs#pkgsCross.riscv64-musl.stdenv.cc` (the sources → committed
  binaries direction).  Layout drift fails for both sides; a changed target
  program fails too; the source's GCC-version drift is a warning, as above.
  The committed binaries are never rewritten by CI — the script builds into
  `.lake/e2e/rwx/` and compares.
- **`probe-source`** — manual (`workflow_dispatch`), not part of the gate:
  builds only the source with nixpkgs' cross GCC (a cached download on the
  Linux runner) and requires the **program bytes** to match the committed
  binary (`--only=source --require-source-program`).  Green answers "this
  compiler reproduces the program the proof walks" — which is what would let
  the source's program bytes become a hard gate by default; red means the
  committed binary came from some other GCC, and the log says how far off.
  (The 2021 musl.cc tarball is ruled out as the origin: `ldflags.txt` passes
  `-Wl,--no-warn-rwx-segments`, which binutils only accepts from 2.39.)

## Why the image is page-rounded

The source image's segment is `0x10000 + 0x1000` even though the ELF's
`p_memsz` is `0xf0`.  That is not padding for convenience: the kernel maps
whole pages (`Run.segment_reservation` reserves exactly those), and the pages
are a **file** mapping, so the bytes around the segment come from the file —
the ELF header and program header table before `p_vaddr`, and (for a
`p_memsz == p_filesz` segment) whatever file bytes follow it inside the last
page.  `Common/ElfImage` implements `elf_load`'s computation, which is why the
embedded image needs no post-processing.
