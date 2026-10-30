#!/usr/bin/env bash
# Build the whole port and run the checked-in conformance tests.
# The tests are ordinary Lean theorems, so `lake build` is the test run.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== lake build (library, tests, decoder) =="
lake build

echo "== no escape hatches in the library =="
if grep -RIn --include='*.lean' -E '\b(sorry|axiom)\b' LinuxSem/; then
  echo "found sorry/axiom in LinuxSem/" >&2
  exit 1
fi

echo "== axiom audit (catches goal-dropping tactics) =="
# The audit must ELABORATE, not merely avoid printing `sorryAx`: a stale name
# in it fails with an unknown-identifier error, which the old
# `grep -q sorryAx` guard could not distinguish from a clean run.
audit=$(lake env lean scripts/AxiomAudit.lean 2>&1) || {
  printf '%s\n' "$audit" >&2
  echo "axiom audit did not elaborate (stale name, or a hole)" >&2
  exit 1
}
if printf '%s\n' "$audit" | grep -q "sorryAx"; then
  echo "a checked theorem depends on sorryAx" >&2
  exit 1
fi

echo "== decoder smoke test =="
out=$(printf '0x00000013\n0x8082\n' | ./.lake/build/bin/decoder)
echo "$out"
echo "$out" | grep -q "opImm" || { echo "decoder smoke test failed" >&2; exit 1; }

echo "OK"
