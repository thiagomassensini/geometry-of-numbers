#!/usr/bin/env bash
# Source-first physical C2 Pick 3×3 strict PD checkpoint.
# Usage: validate-physical-three.sh /path/to/carry-self-adjoint-operator
set -euo pipefail
gon="$(cd "$(dirname "$0")/../.." && pwd)"
if [ "$#" -lt 1 ]; then
  echo "Usage: $0 /path/to/carry-self-adjoint-operator" >&2
  exit 2
fi
csa="$(cd "$1" && pwd)"
python3 - "$gon" "$csa" <<'PY'
import json, pathlib, sys
gon,csa=map(pathlib.Path,sys.argv[1:])
assert (gon/"lean-toolchain").read_bytes() == (csa/"lean-toolchain").read_bytes()
def pins(root):
    d=json.loads((root/"lake-manifest.json").read_text())
    return {pkg["name"]:pkg["rev"] for pkg in d["packages"]
            if pkg["name"] in ("mathlib","GreenFrame")}
assert pins(gon) == pins(csa), (pins(gon),pins(csa))
print("PASS: same Lean toolchain and shared mathlib/GreenFrame pins.")
PY
(cd "$gon" && lake build GeometryOfNumbers.Analysis.CarryMaterialPickThreeSchurCriterion >/dev/null)
csa_path="$(cd "$csa" && lake env printenv LEAN_PATH)"
lean_exe="$(cd "$csa" && lake env sh -c 'command -v lean')"
log="/tmp/gon-c2-physical-three-lean-validation.log"
LEAN_PATH="$gon/.lake/build/lib/lean:$csa_path" "$lean_exe" -DwarningAsError=true \
  -o "$gon/.lake/build/lib/lean/PhysicalPickTwoStrictNative.olean" \
  "$gon/research/material-central-calibration/PhysicalPickTwoStrictNative.lean" \
  > "$log" 2>&1
LEAN_PATH="$gon/.lake/build/lib/lean:$csa_path" "$lean_exe" -DwarningAsError=true \
  "$gon/research/material-central-calibration/CanonicalComparison.lean" >> "$log" 2>&1
if grep -Eq 'error:|sorryAx' "$log"; then
  tail -60 "$log" >&2
  exit 1
fi
for decl in \
  'canonicalCompletedNativeRadialDslopeSampleMatrix_two_det_eventually_ne_zero' \
  'physicalC2RadialPickMatrix_two_eventually_posDef' \
  'physicalC2RadialPickMatrix_three_eventually_posDef' \
  'physicalC2RadialDefectMatrix_three_eventually_posDef'; do
  grep -q "$decl' depends on axioms" "$log" || { echo "Missing audit: $decl"; exit 1; }
done
grep -A2 -E 'physicalC2Radial(PickMatrix|DefectMatrix)_three_eventually_posDef' "$log"
echo "PASS: physical C2 strict radial Pick 3×3 and chiral defect 3×3."
