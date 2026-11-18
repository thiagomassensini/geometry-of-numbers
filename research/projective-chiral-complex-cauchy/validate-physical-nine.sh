#!/usr/bin/env bash
# Reproduce the physical material C2 nine-point strict Pick / multiplier gate.
# Usage: validate-physical-nine.sh /path/to/carry-self-adjoint-operator
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
           GeometryOfNumbers.Analysis.CarryMaterialPickSevenParity \
           GeometryOfNumbers.Analysis.CarryMaterialPickSevenSchurCriterion \
           GeometryOfNumbers.Analysis.CarryMaterialPickEightParity \
           GeometryOfNumbers.Analysis.CarryMaterialPickEightSchurCriterion \
           GeometryOfNumbers.Analysis.CarryMaterialPickNineParity \
           GeometryOfNumbers.Analysis.CarryMaterialPickNineSchurCriterion \
           GeometryOfNumbers.Analysis.CarryMaterialPickFourParity \
           GeometryOfNumbers.Analysis.CarryMaterialPickFourSchurCriterion \
           >/tmp/gon-c2-nine-module-validation.log 2>&1
csa_path="$(cd "$csa" && lake env printenv LEAN_PATH)"
lean_exe="$(cd "$csa" && lake env sh -c 'command -v lean')"
# The original source K4 certificate is a previously audited GoN
# research module, with research .olean dependencies, not a Lake dependency.
for oldcert in   "$gon/.lake/build/research/critical-source-return/KnownMargins.olean"   "$gon/.lake/build/research/theta-fifth-odd-pattern/TenSourceReturn.olean"; do
  test -f "$oldcert" || { echo "Missing prior source certificate $oldcert" >&2; exit 3; }
done
research_path="$(find "$gon/.lake/build/research" -type f -name '*.olean' -printf '%h\n' |
  grep -v 'pr38-lib' | sort -u | paste -sd: -)"
log="/tmp/gon-c2-nine-physical-validation.log"
: > "$log"
lean_compile () {
  local module="$1"
  LEAN_PATH="$gon/.lake/build/lib/lean:$research_path:$csa_path" "$lean_exe" \
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
  PhysicalPickSixCongruence PhysicalPickSixSign PhysicalPickSixFinal \
  PhysicalPickSevenEvenSourceHankel PhysicalPickSevenNative \
  PhysicalPickSevenCongruence PhysicalPickSevenSign PhysicalPickSevenFinal \
  PhysicalPickEightOddSourceHankel PhysicalPickEightDiscriminantBridge \
  PhysicalPickEightNative PhysicalPickEightCongruence \
  PhysicalPickEightSign PhysicalPickEightFinal \
  PhysicalPickNineEvenSourceHankel PhysicalPickNineEvenSignBridge \
  PhysicalPickNineSchurDetLaw PhysicalPickNineRelativeSourceAngle PhysicalPickNinePhysicalBoundary PhysicalPickNineNative \
  PhysicalPickNineCongruence PhysicalPickNineSign PhysicalPickNineFinal; do
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
  physicalC2RadialDefectMatrix_six_eventually_posDef \
  canonical_native_unshifted_hankel_four_det_pos \
  c2_seven_parity_determinant \
  polarizedGreenMomentCoefficient_seven_det \
  canonicalCompletedNativeRadialSevenPointDifferenceMatrix_det_eventually_re_pos \
  completedGreenSevenPointDifference_congruence \
  canonicalCompletedNativeRadialDslopeSampleMatrix_seven_det_eventually_re_pos \
  physicalC2RadialPickMatrix_seven_eventually_posDef \
  physicalC2RadialDefectMatrix_seven_eventually_posDef \
  canonicalCompletedNativeShiftedHankel_four_det_pos \
  nativeSourceEightOddDiscriminant_eq_nativeHankel_four_det \
  nativeSourceEightOddDiscriminant_eq_sixteen_shiftedHankel_four_det \
  nativeSourceEightOddDiscriminant_pos \
  nativeSourceEightOddMargin_eq_two_shiftedHankel_ratio \
  nativeSourceEightOddMargin_pos \
  nativeSourceEightCharacteristicCoefficient_lt_ceiling \
  nativeSourceEightOddBoundaryEnergy_strict_pos \
  c2_eight_parity_determinant \
  hermitian_fin_eight_posDef_of_leading_posDef_det_pos \
  polarizedGreenMomentCoefficient_eight_det \
  canonicalCompletedNativeRadialEightPointDifferenceMatrix_det_eventually_re_pos \
  completedGreenEightPointDifference_congruence \
  canonicalCompletedNativeRadialDslopeSampleMatrix_eight_det_eventually_re_pos \
  physicalC2RadialPickMatrix_eight_eventually_posDef \
  physicalC2RadialDefectMatrix_eight_eventually_posDef \
  canonicalCompletedNativeUnshiftedHankel_five_det_pos \
  canonicalCompletedNativeUnshiftedHankel_five_det_eq_factor_sq \
  nativeSourceNineEvenRawDiscriminant_eq_thirtytwo_hankel_five_det \
  nativeSourceSevenEvenDiscriminant_eq_sixteen_hankel_four_det \
  nativeSourceNineEvenRawRatio_eq_two_hankel_ratio \
  nativeSourceNineEvenRawDiscriminant_pos \
  nativeEvenFiveDet_eq_four_det_mul_sourceSchur \
  nativeSourceNineEvenRawRatio_eq_twice_originalPivot \
  nativeNineEvenCouplingEnergy_nonneg \
  nativeNineEvenNormalizedCoupling_range \
  nativeNineEvenNormalizedResidual_pos_le_one \
  nativeNineEvenNormalizedPartition \
  nativeSourceNineEvenOriginalPivot_pos \
  nativeSourceNineEvenOriginalQuadratic_sewing \
  nativeSourceNineEvenCriticalDirection_energy \
  nativeSourceNineCompleteBoundaryEnergy_pos \
  nativeSourceNineReturn_eventually_contractive \
  c2_nine_parity_determinant \
  hermitian_fin_nine_posDef_of_leading_posDef_det_pos \
  polarizedGreenMomentCoefficient_nine_det \
  canonicalCompletedNativeRadialNinePointDifferenceMatrix_det_eventually_re_pos \
  completedGreenNinePointDifference_congruence \
  canonicalCompletedNativeRadialDslopeSampleMatrix_nine_det_eventually_re_pos \
  physicalC2RadialPickMatrix_nine_eventually_posDef \
  physicalC2RadialDefectMatrix_nine_eventually_posDef; do
  if ! grep -q "$decl' depends on axioms" "$log" &&
     ! grep -q "$decl.*depends on axioms" /tmp/gon-c2-nine-module-validation.log; then
    echo "Missing axiom audit: $decl" >&2
    exit 1
  fi
done
grep -A2 -E 'physicalC2Radial(PickMatrix|DefectMatrix)_nine_eventually_posDef' "$log"
echo "PASS: ninth physical C2 radial Pick and HB defect are strictly PosDef"
