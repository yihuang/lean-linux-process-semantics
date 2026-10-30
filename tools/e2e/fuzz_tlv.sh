#!/usr/bin/env bash
#
# tools/e2e/fuzz_tlv.sh — check what the FuzzTlv theorems do not say
#
#   1. the committed ELFs are what the source and flags build;
#   2. a real emulator agrees with the model: under qemu-riscv64 the fixed build
#      exits 0 or 2, and the buggy build dies by SIGSEGV.  This tests the MODEL, so
#      a disagreement would mean the semantics is wrong.
#
#   nix-shell -p zig qemu --run 'bash tools/e2e/fuzz_tlv.sh --require-qemu'
#
# Without qemu-riscv64 (macOS has no user-mode QEMU) step 2 is reported as SKIPPED,
# and `--require-qemu` makes that a failure.  `--no-rebuild` skips step 1, for a
# machine with QEMU and no zig.
set -euo pipefail
cd "$(dirname "$0")/../.."          # repository root

EX="LinuxSem/Examples/FuzzTlv"
OUT=".lake/e2e/fuzz_tlv"
mkdir -p "$OUT"

REQUIRE_QEMU=0
REBUILD=1
for arg in "$@"; do
  case "$arg" in
    --require-qemu) REQUIRE_QEMU=1 ;;
    --no-rebuild) REBUILD=0 ;;
    *) echo "usage: $0 [--require-qemu] [--no-rebuild]" >&2; exit 2 ;;
  esac
done

fail() { printf 'FAIL %s\n' "$*" >&2; exit 1; }

if [ "$REBUILD" = 1 ]; then
  command -v zig >/dev/null 2>&1 || fail "no zig on PATH; run under: nix-shell -p zig qemu"
  echo "== rebuild ($(zig version))"
  FLAGS=$(cat "$EX/source/build_flags.txt")
  # shellcheck disable=SC2086
  zig cc $FLAGS -DFIXED "$EX/source/fuzz_tlv.c" -o "$OUT/program.fixed"
  # shellcheck disable=SC2086
  zig cc $FLAGS "$EX/source/fuzz_tlv.c" -o "$OUT/program.buggy"
  for kind in fixed buggy; do
    python3 tools/e2e/compare_elfs.py --rebuilt "$OUT/program.$kind" \
      --committed "$EX/program.$kind.elf" --kind "$kind" --require-program-identical \
      || fail "$kind: the rebuilt binary is not the committed one"
  done
fi

if ! command -v qemu-riscv64 >/dev/null 2>&1; then
  [ "$REQUIRE_QEMU" = 1 ] && fail "no qemu-riscv64 on PATH, and --require-qemu was given"
  echo "SKIPPED: no qemu-riscv64 on PATH, so the model's verdicts were NOT compared"
  exit 0
fi
echo "== run under $(qemu-riscv64 --version | head -n 1)"

cp "$EX/program.fixed.elf" "$OUT/run.fixed"
cp "$EX/program.buggy.elf" "$OUT/run.buggy"
chmod +x "$OUT/run.fixed" "$OUT/run.buggy"

expect() {  # expect <binary> <input-file> <allowed statuses...>
  local bin=$1 input=$2 rc=0
  shift 2
  qemu-riscv64 "$bin" <"$input" >/dev/null 2>&1 || rc=$?
  for ok in "$@"; do
    [ "$rc" = "$ok" ] && { echo "  $(basename "$bin") < $(basename "$input"): exit $rc"; return 0; }
  done
  fail "$(basename "$bin") < $(basename "$input"): exit $rc, expected one of: $*"
}

T="$OUT/inputs"
rm -rf "$T"; mkdir -p "$T"
python3 - "$T" <<'PY'
import os, random, sys
root = sys.argv[1]
head = b"\0" * 6
def put(name, data):
    with open(os.path.join(root, name), "wb") as f:
        f.write(data)
put("empty", b"")
put("short", b"abc")
put("header_only", head)
put("one_record", head + b"\x01\x03abc")
put("record_past_data", head + b"\x01\xff" + b"x" * 10)
put("record_past_buffer", head + b"\x01\xfa" + b"y" * 247)
put("oversize", b"z" * 4096)
rng = random.Random(0xf022)
for i in range(32):
    put("random_%02d" % i, bytes(rng.randrange(256) for _ in range(rng.randrange(300))))
PY

for f in "$T"/*; do
  expect "$OUT/run.fixed" "$f" 0 2
done
# Each input reaches one of the two missing checks.  SIGSEGV is 128 + 11.
expect "$OUT/run.buggy" "$T/empty" 139
expect "$OUT/run.buggy" "$T/record_past_buffer" 139

echo "OK"
