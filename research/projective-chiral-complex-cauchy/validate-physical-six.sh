#!/usr/bin/env bash
# Reproduce the physical material C2 six-point strict Pick / multiplier gate.
# Usage: validate-physical-six.sh /path/to/carry-self-adjoint-operator
# No cross-repository Lake dependency or edits to CSA.
set -euo pipefail
gon="$(cd "$(dirname "$0")/../.." && pwd)"
if [ "$#" -ne 1 ]; then
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
lake build GeometryOfNumbers.Analysis.CarryMaterialPickFiveParity \
           GeometryOfNumbers.Analysis.CarryMaterialPickFiveSchurCriterion \
           GeometryOfNumbers.Analysis.CarryMaterialPickSixParity \
           GeometryOfNumbers.Analysis.CarryMaterialPickSixSchurCriterion \
           GeometryOfNumbers.Analysis.CarryMaterialPickFourParity \
           GeometryOfNumbers.Analysis.CarryMaterialPickFourSchurCriterion \
           >/tmp/gon-c2-six-module-validation.log 2>&1
csa_path="$(cd "$csa" && lake env printenv LEAN_PATH)"
lean_exe="$(cd "$csa" && lake env sh -c 'command -v lean')"
log="/tmp/gon-c2-six-physical-validation.log"
: > "$log"
lean_compile () {
  local module="$1"
  LEAN_PATH="$gon/.lake/build/lib/lean:$csa_path" "$lean_exe" \
    -DwarningAsError=true \
    -o "$gon/.lake/build/lib/lean/$module.olean" \
    "$gon/research/material-central-calibration/$module.lean" >>"$log" 2>&1
}
# The preexisting GoN–CSA comparator must be built before the
# fifth-order sign extracted from its material source factor.
for mod in PhysicalPickTwoStrictNative PhysicalPickFourNative \
  PhysicalPickFourCongruence PhysicalPickFourSign CanonicalComparison \
  PhysicalPickFiveSourceHankel PhysicalPickFiveNative \
  PhysicalPickFiveCongruence PhysicalPickFiveSign PhysicalPickFiveFinal \
  PhysicalPickSixOddSourceHankel PhysicalPickSixNative \
  PhysicalPickSixCongruence PhysicalPickSixSign PhysicalPickSixFinal; do
  lean_compile "$mod"
done
if grep -Eq 'error:|sorryAx' "$log"; then
  tail -60 "$log" >&2
  exit 1
fi
for decl in \
  canonical_native_unshifted_hankel_three_det_pos \
  c2_five_parity_determinant \
  polarizedGreenMomentCoefficient_five_det \
  canonicalCompletedNativeRadialFivePointDifferenceMatrix_det_eventually_re_pos \
  completedGreenFivePointDifference_congruence \
  canonicalCompletedNativeRadialDslopeSampleMatrix_five_det_eventually_re_pos \
  nativeSourceSixOddDiscriminant_eq_eight_shiftedHankel_three_det \
  canonicalCompletedNativeShiftedHankel_three_det_pos \
  c2_six_parity_determinant \
  polarizedGreenMomentCoefficient_six_det \
  canonicalCompletedNativeRadialSixPointDifferenceMatrix_det_eventually_re_pos \
  completedGreenSixPointDifference_congruence \
  canonicalCompletedNativeRadialDslopeSampleMatrix_six_det_eventually_re_pos \
  physicalC2RadialPickMatrix_six_eventually_posDef \
  physicalC2RadialDefectMatrix_six_eventually_posDef; do
  if ! grep -q "$decl' depends on axioms" "$log" &&
     ! grep -q "$decl.*depends on axioms" /tmp/gon-c2-six-module-validation.log; then
    echo "Missing axiom audit: $decl" >&2
    exit 1
  fi
done
grep -A2 -E 'physicalC2Radial(PickMatrix|DefectMatrix)_six_eventually_posDef' "$log"
echo "PASS: sixth physical C2 radial Pick and HB defect are strictly PosDef"
