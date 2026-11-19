#!/usr/bin/env bash
# Reproduce the fourth radial physical C2 Pick PD certificate.
# Usage: validate-physical-four.sh /path/to/carry-self-adjoint-operator
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
print("PASS: Lean toolchain and mathlib/GreenFrame pins match")
PY
cd "$gon"
lake build GeometryOfNumbers.Analysis.CarryMaterialPickFourParity \
  GeometryOfNumbers.Analysis.CarryMaterialPickFourSchurCriterion >/tmp/gon-c2-four-modules.log 2>&1
csa_path="$(cd "$csa" && lake env printenv LEAN_PATH)"
lean_exe="$(cd "$csa" && lake env sh -c 'command -v lean')"
log="/tmp/gon-c2-four-physical-validation.log"
: >"$log"
for p in \
  PhysicalPickTwoStrictNative \
  PhysicalPickFourNative \
  PhysicalPickFourCongruence \
  PhysicalPickFourSign; do
  LEAN_PATH="$gon/.lake/build/lib/lean:$csa_path" "$lean_exe" \
    -DwarningAsError=true \
    -o "$gon/.lake/build/lib/lean/$p.olean" \
    "$gon/research/material-central-calibration/$p.lean" >> "$log" 2>&1
done
LEAN_PATH="$gon/.lake/build/lib/lean:$csa_path" "$lean_exe" \
  -DwarningAsError=true \
  "$gon/research/material-central-calibration/CanonicalComparison.lean" >> "$log" 2>&1
if grep -Eq 'error:|sorryAx' "$log"; then
  tail -60 "$log" >&2
  exit 1
fi
for decl in \
  polarizedGreenMomentCoefficient_four_det \
  canonicalCompletedNativeRadialFourPointDifferenceMatrix_det_eventually_re_pos \
  completedGreenFourPointDifference_congruence \
  canonicalCompletedNativeRadialDslopeSampleMatrix_four_det_eventually_re_pos \
  physicalC2RadialPickMatrix_four_eventually_posDef \
  physicalC2RadialDefectMatrix_four_eventually_posDef; do
  grep -q "$decl' depends on axioms" "$log" || {
    echo "Missing audit declaration: $decl" >&2
    exit 1
  }
done
grep -A2 -E 'physicalC2Radial(PickMatrix|DefectMatrix)_four_eventually_posDef' "$log"
echo "PASS: fourth physical C2 Pick and chiral multiplier defect are strictly PD"
