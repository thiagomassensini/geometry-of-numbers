import PivotFromIntegral

namespace CarryIntegralCertificate
open GeometryOfNumbers.Analysis
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536

/-- Closed integer calculation, reduced and checked by the kernel. -/
theorem fourthPivot_rectangle_check : (remainderBox 3 3 3).positive = true := by
  decide +kernel

theorem material_fourth_positive_of_integral_inputs
    (hb : ∀ n, (momentInputBox n).Mem
      (CarrySelfAdjointOperator.completedNativeThetaTailMoment (2*n))) :
    0 < carryMaterialFourthPivot := by
  exact pos_of_mem (mem_remainderBox hb 3 3 3) fourthPivot_rectangle_check

/-- Closed checks of a comfortable quantitative margin; no floating-point arithmetic. -/
theorem fourthPivot_lower_margin_check :
    ((remainderBox 3 3 3).add (Box.rat 16 (10^27)).neg).positive = true := by
  decide +kernel

theorem fourthPivot_upper_margin_check :
    ((Box.rat 17 (10^27)).add (remainderBox 3 3 3).neg).positive = true := by
  decide +kernel

theorem material_fourth_bounds_of_integral_inputs
    (hb : ∀ n, (momentInputBox n).Mem
      (CarrySelfAdjointOperator.completedNativeThetaTailMoment (2*n))) :
    (16/10^27:ℝ) < carryMaterialFourthPivot ∧ carryMaterialFourthPivot < (17/10^27:ℝ) := by
  have hm := mem_remainderBox hb 3 3 3
  have hl := pos_of_mem (mem_add hm (mem_neg (mem_rat 16 (10^27)))) fourthPivot_lower_margin_check
  have hu := pos_of_mem (mem_add (mem_rat 17 (10^27)) (mem_neg hm)) fourthPivot_upper_margin_check
  norm_num only [Int.cast_ofNat,Int.cast_pow] at hl hu
  change (16/10^27:ℝ) < carryPairingRemainder carryMaterialEvenPairing 3 3 3 ∧
    carryPairingRemainder carryMaterialEvenPairing 3 3 3 < (17/10^27:ℝ)
  constructor <;> linarith only [hl,hu]

end CarryIntegralCertificate
