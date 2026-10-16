#!/usr/bin/env bash
# Read-only comparison against the operator checkout; no dependency/pin changes.
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
operator_root="${1:?usage: audit-material-central-comparison.sh /path/to/carry-self-adjoint-operator}"
operator_root="$(cd -- "$operator_root" && pwd)"
expected_operator=045369f6dedcb2e75e9aefed1d12c9f73b9a2532
actual_operator="$(git -C "$operator_root" rev-parse HEAD)"
if [[ "$actual_operator" != "$expected_operator" ]]; then
  echo "ERROR: comparison was audited at operator $expected_operator; found $actual_operator" >&2
  exit 1
fi
python3 - "$root" "$operator_root" <<'PY'
import json, pathlib, sys
a, b = map(pathlib.Path, sys.argv[1:])
assert (a/'lean-toolchain').read_bytes() == (b/'lean-toolchain').read_bytes(), 'Lean pins differ'
def pins(p):
    return {x['name']: x['rev'] for x in json.loads((p/'lake-manifest.json').read_text())['packages'] if x['name'] in ('mathlib', 'GreenFrame')}
pa, pb = pins(a), pins(b)
assert len(pa) == 2 and pa == pb, f'shared dependency pins differ: {pa} != {pb}'
print('PASS: identical Lean, Mathlib and GreenFrame pins; operator HEAD checked')
PY
cd -- "$root"
lean_cmd="$(lake env sh -c 'command -v lean')"
operator_lpath="$(cd -- "$operator_root" && lake env printenv LEAN_PATH)"
# Run in the operator directory: its Lake paths may be relative. The geometry
# library path is absolute and is placed first; shared pins were checked above.
cd -- "$operator_root"
LEAN_PATH="$root/.lake/build/lib/lean:$operator_lpath" \
  "$lean_cmd" -DwarningAsError=true "$root/research/material-central-calibration/CanonicalComparison.lean"
echo 'PASS: scalar source identification, central defect and normalized-kernel obstruction; all transitive axiom guards passed'
