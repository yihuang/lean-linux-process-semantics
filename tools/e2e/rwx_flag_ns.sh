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
#   layout + bytes identical           -> reproduced exactly (exit 0)
#   layout identical, bytes differ     -> right recipe, same image shape, but
#                                         this host's compiler emitted a
#                                         different program / section table;
#                                         the committed binary is pinned to the
#                                         upstream build (exit 0, WARN)
#   layout differs                     -> the recipe or the binary is wrong
#                                         (exit 1)
#
# `--strict-bytes` turns the WARN case into a failure, which is what a
# reproducibility gate should do on a host with the upstream toolchain.
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
[ "${1:-}" = "--strict-bytes" ] && STRICT_BYTES=1

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
  rc=0
  python3 tools/e2e/compare_elfs.py \
      --rebuilt "$OUT/program.$tag" --committed "$EX/program.$tag.elf" \
      --kind "$kind" || rc=$?
  case $rc in
    0) echo "  $kind: committed binary REPRODUCED exactly" ;;
    2)
      drift=1
      if [ "$kind" = source ] && [ "$SRC_TOOLCHAIN" = fallback ]; then
        warn "source: the committed binary is the GNU riscv64-linux-musl-gcc"
        warn "build; this host used zig cc (clang), so the instructions differ."
        warn "Install riscv64-linux-musl-gcc (or set SOURCE_CC) to reproduce it."
      else
        warn "$kind: same image LAYOUT and a different section table / bytes;"
        warn "see the per-segment lines above (the program's own file extents"
        warn "are often identical while the page slack is not)."
      fi ;;
    *) fail "$kind: the rebuilt binary has a DIFFERENT LAYOUT from the committed one" ;;
  esac
done

if [ "$drift" = 1 ] && [ "$STRICT_BYTES" = 1 ]; then
  fail "byte-identical reproduction was requested (--strict-bytes) and failed"
fi

echo "OK (layout verified; see WARN lines above for byte-level toolchain drift)"
