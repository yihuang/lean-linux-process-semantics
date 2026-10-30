#!/usr/bin/env bash
#
# tools/e2e/rwx_flag_ns.sh — rebuild the RwxFlagNs example from its SOURCES
#
# The committed artifacts are the two BINARIES:
#
#   source/program.c   --riscv64-linux-musl-gcc-->  program.src.elf
#   target/program.zig --zig build-exe---------->  program.tgt.elf
#
# and `SourceMemImage.lean`/`TargetMemImage.lean` read those files at
# elaboration time (`embedElf%`, Common/EmbedElf → Common/ElfImage).  This
# script rebuilds both with the command lines the upstream repository
# documents, then compares each rebuilt binary with its committed counterpart
# AT THE LOADER LEVEL (tools/e2e/compare_elfs.py): the page-rounded segment
# extents and permissions, the entry point, the AT_PHDR the kernel derives, and
# then the bytes — per PT_LOAD, its own file extent separately from the page
# slack around it.
#
# WHAT THE COMPARISON MEANS
#
#   layout identical, program bytes identical   -> exit 0 (the image is the same
#       program; only the section header table, which the loader never reads and
#       the program never touches, moved)
#   layout identical, page images identical     -> exit 0 (exact reproduction)
#   layout identical, program bytes differ      -> FAIL, unless the side was
#       built by the FALLBACK compiler: the committed source binary comes from
#       GNU riscv64-linux-musl-gcc, and `zig cc` (clang) emits a different
#       program.  Then the layout is still gated and the drift is a WARN.
#   layout differs                              -> FAIL (the recipe or the
#       committed binary is wrong)
#
# The "program bytes" check masks the ELF header's section-table bookkeeping
# (`e_shoff`/`e_shentsize`/`e_shnum`/`e_shstrndx`) and looks only at each
# PT_LOAD's own file extent: that is what a CI gate can hold across compiler
# versions.  `--strict-bytes` instead demands the page images be byte-identical
# (what a host with the upstream toolchains can achieve), and
# `--allow-program-drift` drops the program check entirely (for trying a
# different toolchain).
#
# THE SOURCE COMPILER.  The committed source binary is a GNU
# riscv64-linux-musl-gcc build (see source/ldflags.txt and the `_start.S` in
# LinuxSem/Examples/crt/).  If that compiler is not installed, the script falls
# back to `zig cc`, which cannot link with `-nostartfiles` (zig's driver always
# adds its own crt1.o) and is clang-based, so it produces a DIFFERENT program
# with the same layout.  The fallback defines the one symbol the crt needs from
# musl (`environ`) in LinuxSem/Examples/crt/environ.S.  Override the compiler
# with SOURCE_CC=...
set -euo pipefail
cd "$(dirname "$0")/../.."          # repository root

EX="LinuxSem/Examples/RwxFlagNs"
OUT=".lake/e2e/rwx"
mkdir -p "$OUT"
ROOT="$(pwd)"

STRICT_BYTES=0
ALLOW_PROGRAM_DRIFT=0
for arg in "$@"; do
  case "$arg" in
    --strict-bytes) STRICT_BYTES=1 ;;
    --allow-program-drift) ALLOW_PROGRAM_DRIFT=1 ;;
    *) echo "usage: $0 [--strict-bytes | --allow-program-drift]" >&2; exit 2 ;;
  esac
done

ZIG="${ZIG:-zig}"
SOURCE_CC="${SOURCE_CC:-riscv64-linux-musl-gcc}"
warn() { printf '\033[33mWARN\033[0m %s\n' "$*"; }
fail() { printf '\033[31mFAIL\033[0m %s\n' "$*" >&2; exit 1; }

# ---------------------------------------------------------------- 1. source
echo "== 1/3  source: $EX/source/program.c"
if command -v "$SOURCE_CC" >/dev/null 2>&1; then
  echo "         with $SOURCE_CC (the upstream toolchain)"
  ( cd "$EX/source" && "$SOURCE_CC" -std=gnu17 -march=rv64imafd -Os -static \
      -nostartfiles -fno-builtin -fno-strict-aliasing \
      $(grep -hv '^#' ldflags.txt) \
      ../../crt/_start.S program.c -o "$ROOT/$OUT/program.src" )
  SRC_TOOLCHAIN=upstream
else
  warn "no $SOURCE_CC on PATH: falling back to zig cc (clang codegen, and"
  warn "no -nostartfiles support, so crt/environ.S supplies musl's environ)."
  warn "The image will have the same LAYOUT and a different program."
  ( cd "$EX/source" && "$ZIG" cc -target riscv64-linux-musl -mcpu=baseline_rv64-c \
      -std=gnu17 -Os -static -nostdlib -fno-builtin -fno-strict-aliasing \
      -Wl,-T,rwx.lds \
      ../../crt/_start.S ../../crt/environ.S program.c \
      -o "$ROOT/$OUT/program.src" )
  SRC_TOOLCHAIN=fallback
fi

# ---------------------------------------------------------------- 2. target
echo "== 2/3  target: $EX/target/program.zig"
# the upstream command line: zig build-exe, freestanding, flags from flags.txt
TGT_FLAGS=$(grep -hv '^#' "$EX/target/flags.txt" | tr '\n' ' ')
# shellcheck disable=SC2086
"$ZIG" build-exe "$EX/target/program.zig" $TGT_FLAGS \
  -target riscv64-linux-none -femit-bin="$OUT/program.tgt"

# ---------------------------------------------------------------- 3. compare
echo "== 3/3  compare the rebuilt binaries with the committed ones (loader level)"
drift=0
for pair in "src:source" "tgt:target"; do
  tag=${pair%%:*}; kind=${pair##*:}
  # Program identity is required for the target (same compiler family), and
  # for the source when it was built by the documented GNU compiler.  With the
  # `zig cc` fallback the source program is known to differ (clang vs gcc), so
  # only its layout is gated there.
  require_program=0
  if [ "$STRICT_BYTES" = 0 ] && [ "$ALLOW_PROGRAM_DRIFT" = 0 ]; then
    if [ "$kind" = target ] || [ "$SRC_TOOLCHAIN" = upstream ]; then
      require_program=1
    fi
  fi
  args=(--rebuilt "$OUT/program.$tag" --committed "$EX/program.$tag.elf" --kind "$kind")
  [ "$require_program" = 1 ] && args+=(--require-program-identical)

  rc=0
  python3 tools/e2e/compare_elfs.py "${args[@]}" || rc=$?
  case $rc in
    0)
      if [ "$STRICT_BYTES" = 1 ]; then
        echo "  $kind: committed binary REPRODUCED exactly"
      elif [ "$require_program" = 1 ]; then
        echo "  $kind: layout + program bytes REPRODUCED (section table ignored)"
      else
        echo "  $kind: layout REPRODUCED (byte-level drift reported above)"
      fi ;;
    2)
      drift=1
      if [ "$kind" = source ] && [ "$SRC_TOOLCHAIN" = fallback ]; then
        warn "source: the committed binary is the GNU riscv64-linux-musl-gcc"
        warn "build; this host used zig cc (clang), so the instructions differ."
        warn "Install riscv64-linux-musl-gcc (or set SOURCE_CC) to reproduce it."
        warn "Layout is verified; the program bytes are not gated on this host."
      elif [ "$STRICT_BYTES" = 1 ]; then
        warn "$kind: page images differ (--strict-bytes measures exactly that;"
        warn "only the upstream toolchains reproduce them)."
      else
        warn "$kind: same image LAYOUT and different page bytes; see the"
        warn "per-segment lines above."
      fi ;;
    3)
      fail "$kind: the rebuilt binary is a DIFFERENT PROGRAM from the committed one (see above); re-baseline it or pass --allow-program-drift" ;;
    *) fail "$kind: the rebuilt binary has a DIFFERENT LAYOUT from the committed one" ;;
  esac
done

if [ "$drift" = 1 ] && [ "$STRICT_BYTES" = 1 ]; then
  fail "byte-identical reproduction was requested (--strict-bytes) and failed"
fi

if [ "$drift" = 1 ]; then
  echo "OK (layout verified; see WARN lines above for byte-level toolchain drift)"
else
  echo "OK"
fi
