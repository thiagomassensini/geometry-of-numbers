import SignalBounds

namespace CarryReadoutBounds
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryFourthTail CarryMaterialParts
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem log_two_bounds : (1/2:ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

theorem power_two_lower {x : ℝ} (hx : 1/4 ≤ x) : (9/8:ℝ) ≤ (2:ℝ)^x := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have h := Real.add_one_le_exp (Real.log 2*x)
  have ht := log_two_bounds.1
  nlinarith

theorem camera_power_bounds (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖(2:ℂ)^(-baseTwoDressingParameter w)‖ ≤ 8/9 ∧
    (9/8:ℝ) ≤ ‖(2:ℂ)^(1-baseTwoDressingParameter w)‖ ∧
    ‖(2:ℂ)^(1-baseTwoDressingParameter w)‖ ≤ 2 := by
  obtain ⟨hl,hu,_⟩ := gamma_argument_bounds w hw
  have hs : (1/4:ℝ) ≤ (baseTwoDressingParameter w).re ∧
      (baseTwoDressingParameter w).re ≤ 3/4 := by
    norm_num [Complex.div_re] at hl hu
    constructor <;> linarith
  simp only [show (2:ℂ)=((2:ℝ):ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2), Complex.neg_re,
    Complex.sub_re, Complex.one_re]
  constructor
  · rw [Real.rpow_neg (by norm_num), inv_eq_one_div]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)).2
      (by nlinarith [power_two_lower hs.1])
  constructor
  · exact power_two_lower (by linarith)
  · exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (show 1-(baseTwoDressingParameter w).re ≤ 1 by linarith)).trans_eq (Real.rpow_one 2)

theorem camera_inverse_factors (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    (1/9:ℝ) ≤ ‖1+(2:ℂ)^(-baseTwoDressingParameter w)‖ ∧
    (1/8:ℝ) ≤ ‖1-(2:ℂ)^(1-baseTwoDressingParameter w)‖ := by
  obtain ⟨hu,hv,_⟩ := camera_power_bounds w hw
  have h1 := norm_sub_le (1+(2:ℂ)^(-baseTwoDressingParameter w))
    ((2:ℂ)^(-baseTwoDressingParameter w))
  have h2 := norm_sub_le (1:ℂ) (1-(2:ℂ)^(1-baseTwoDressingParameter w))
  simp only [add_sub_cancel_right, norm_one, sub_sub_cancel] at h1 h2
  constructor <;> linarith

theorem camera_complex_nonzero (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    baseTwoCanonicalCameraFactorComplex w ≠ 0 := by
  obtain ⟨h1,h2⟩ := camera_inverse_factors w hw
  exact mul_ne_zero (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) h1))
    (norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) h2))

theorem camera_complex_bound (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖baseTwoCanonicalCameraFactorComplex w‖ ≤ 6 := by
  obtain ⟨hu,_,hv⟩ := camera_power_bounds w hw
  have h1 := norm_add_le (1:ℂ) ((2:ℂ)^(-baseTwoDressingParameter w))
  have h2 := norm_sub_le (1:ℂ) ((2:ℂ)^(1-baseTwoDressingParameter w))
  norm_num only [norm_one] at h1 h2
  unfold baseTwoCanonicalCameraFactorComplex
  rw [norm_mul]
  nlinarith [norm_nonneg (1+(2:ℂ)^(-baseTwoDressingParameter w)),
    norm_nonneg (1-(2:ℂ)^(1-baseTwoDressingParameter w)), mul_le_mul h1 h2 (norm_nonneg _) (by positivity)]

theorem camera_complex_inverse_bound (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖(baseTwoCanonicalCameraFactorComplex w)⁻¹‖ ≤ 72 := by
  obtain ⟨h1,h2⟩ := camera_inverse_factors w hw
  unfold baseTwoCanonicalCameraFactorComplex
  rw [norm_inv, norm_mul, inv_eq_one_div]
  apply (div_le_iff₀ (mul_pos (lt_of_lt_of_le (by norm_num) h1)
    (lt_of_lt_of_le (by norm_num) h2))).2
  nlinarith [mul_le_mul h1 h2 (by norm_num : (0:ℝ)≤1/8) (norm_nonneg _)]

end
end CarryReadoutBounds
