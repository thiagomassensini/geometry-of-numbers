#!/usr/bin/env bash
# External GoN↔CSA comparison; no manifest/pin mutations.
set -euo pipefail
gon_root="$(cd -- "$(dirname -- "$0")/../.." && pwd)"
if [ "$#" -lt 1 ]; then
  echo "usage: validate.sh /path/to/csa-worktree-with-PR128" >&2
  exit 2
fi
csa_root="$(cd -- "$1" && pwd)"
python3 - "$gon_root" "$csa_root" <<'PY'
import pathlib, json, sys
gon,csa=map(pathlib.Path,sys.argv[1:])
assert (gon/'lean-toolchain').read_bytes()==(csa/'lean-toolchain').read_bytes()
def pins(p):
    d=json.loads((p/'lake-manifest.json').read_text())
    return {x['name']:x['rev'] for x in d['packages'] if x['name'] in ('mathlib','GreenFrame')}
assert pins(gon)==pins(csa), (pins(gon),pins(csa))
assert (csa/'CarrySelfAdjointOperator/RealAxisWronskianDslopeSewing.lean').exists()
print('Lean toolchain and CSA/GoN shared pins match.')
PY
(cd "$csa_root" && lake build CarrySelfAdjointOperator.RealAxisWronskianDslopeSewing >/dev/null)
(cd "$gon_root" && lake build GeometryOfNumbers.Analysis.CarryMaterialProjectiveChiralSewing >/dev/null)
operator_lpath="$(cd "$csa_root" && lake env printenv LEAN_PATH)"
lean_cmd="$(cd "$csa_root" && lake env sh -c 'command -v lean')"
log="$gon_root/research/projective-chiral-physical-sewing/crosscheck.log"
(cd "$csa_root" &&
 LEAN_PATH="$gon_root/.lake/build/lib/lean:$operator_lpath" \
 "$lean_cmd" -DwarningAsError=true \
 "$gon_root/research/material-central-calibration/CanonicalComparison.lean") >"$log" 2>&1
grep -A2 -E "CarryMaterialPhysicalProjectiveChiralComparison.*depends on axioms" "$log" | tail -16
echo 'PASS: physical two-arm C2→completed Wronskian→division-free dslope numerator'
