import ThirdSourcePrefix

namespace CarryOddHeadSource
open CarrySourceBezout CarrySourceDimensionThree CarrySelfAdjointOperator Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- Proposed rational enclosure center for the original completed C3 head. -/
def oddHeadFourthCenter : ℝ := 3992226551344 / 10^21

theorem odd_tail_four_bound : ‖regroupedTail64 4‖ ≤ (2/10^15:ℝ) := by
  rw [regrouped_tail64_jet]
  exact (CarryC3Tail.completed_tail_jet_error 8).trans (by norm_num)

theorem native_c4_upper_of_head_box
    (hbox : ‖regroupedHead64 4 - (oddHeadFourthCenter : ℂ)‖ ≤ (1/10^12:ℝ)) :
    nativeC 4 ≤ (4/10^9:ℝ) := by
  have hs := congrArg Complex.re (regrouped_source 4)
  have hh := (Complex.abs_re_le_norm
    (regroupedHead64 4 - (oddHeadFourthCenter : ℂ))).trans hbox
  have ht := (Complex.abs_re_le_norm (regroupedTail64 4)).trans odd_tail_four_bound
  have hhu := (abs_le.mp hh).2
  have htu := (abs_le.mp ht).2
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re] at hhu hs
  dsimp [oddHeadFourthCenter] at hhu
  norm_num at hhu htu hs ⊢
  linarith

theorem odd_source_det_margin_of_c4_upper
    (hc4 : nativeC 4 ≤ (4/10^9:ℝ)) :
    (9/10^17:ℝ) < (coefficientBlock (sourceKernel nativeC true) 2).det := by
  have h0 := abs_le.mp (native_real_four_reference_bounds 0)
  have h1 := abs_le.mp (native_real_four_reference_bounds 1)
  have h2 := abs_le.mp (native_real_four_reference_bounds 2)
  have h3 := abs_le.mp (native_real_four_reference_bounds 3)
  norm_num [twoEvenReferenceReal] at h0 h1 h2 h3
  have c0l : (497120778187/10^12:ℝ) ≤ nativeC 0 := by norm_num at h0 ⊢; linarith
  have c0u : nativeC 0 ≤ (497120778190/10^12:ℝ) := by norm_num at h0 ⊢; linarith
  have c1l : -(11485972159/10^12:ℝ) ≤ nativeC 1 := by norm_num at h1 ⊢; linarith
  have c1u : nativeC 1 ≤ -(11485972156/10^12:ℝ) := by norm_num at h1 ⊢; linarith
  have c2l : (123452017/10^12:ℝ) ≤ nativeC 2 := by norm_num at h2 ⊢; linarith
  have c2u : nativeC 2 ≤ (123452020/10^12:ℝ) := by norm_num at h2 ⊢; linarith
  have c3l : -(832357/10^12:ℝ) ≤ nativeC 3 := by norm_num at h3 ⊢; linarith
  have c3u : nativeC 3 ≤ -(832354/10^12:ℝ) := by norm_num at h3 ⊢; linarith
  have c0pos : 0 ≤ nativeC 0 := by linarith
  have c2pos : 0 ≤ nativeC 2 := by linarith
  have c1neg : nativeC 1 ≤ 0 := by linarith
  have c3neg : nativeC 3 ≤ 0 := by linarith
  have p02 := mul_le_mul c0u c2u c2pos (by norm_num : (0:ℝ) ≤ 497120778190/10^12)
  have p13 := mul_le_mul (show -nativeC 1 ≤ (11485972159/10^12:ℝ) by linarith)
    (show -nativeC 3 ≤ (832357/10^12:ℝ) by linarith)
    (show 0 ≤ -nativeC 3 by linarith) (by norm_num : (0:ℝ) ≤ 11485972159/10^12)
  have p04 := mul_nonneg c0pos (show 0 ≤ (4/10^9:ℝ) - nativeC 4 by linarith)
  have p12a := mul_nonneg (show 0 ≤ nativeC 1 + (11485972159/10^12:ℝ) by linarith) c2pos
  have p12b := mul_nonneg (by norm_num : (0:ℝ) ≤ 11485972159/10^12)
    (show 0 ≤ (123452020/10^12:ℝ) - nativeC 2 by linarith)
  have p03a := mul_nonneg (show 0 ≤ nativeC 0 - (497120778187/10^12:ℝ) by linarith)
    (show 0 ≤ -nativeC 3 by linarith)
  have p03b := mul_nonneg (by norm_num : (0:ℝ) ≤ 497120778187/10^12)
    (show 0 ≤ -nativeC 3 - (832354/10^12:ℝ) by linarith)
  have ha : (91864/10^10:ℝ) ≤ nativeC 1^2 - 2*nativeC 0*nativeC 2 := by
    nlinarith [sq_nonneg (nativeC 1 + (11485972156/10^12:ℝ))]
  have hd : (3406/10^12:ℝ) ≤ 2*nativeC 2^2 - 2*nativeC 1*nativeC 3 - 4*nativeC 0*nativeC 4 := by
    nlinarith [sq_nonneg (nativeC 2 - (123452017/10^12:ℝ))]
  have hb : |nativeC 1*nativeC 2 - 3*nativeC 0*nativeC 3| ≤ (176625/10^12:ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith
  have hbsq : (nativeC 1*nativeC 2 - 3*nativeC 0*nativeC 3)^2 ≤ (176625/10^12:ℝ)^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (nativeC 1*nativeC 2 - 3*nativeC 0*nativeC 3))
      (by positivity : (0:ℝ) ≤ 176625/10^12)).2 hb
    simpa only [sq_abs] using hh
  have had := mul_le_mul ha hd (by positivity : (0:ℝ) ≤ 3406/10^12)
    (by linarith : 0 ≤ nativeC 1^2 - 2*nativeC 0*nativeC 2)
  rw [source_odd_two, Matrix.det_fin_two]
  norm_num
  nlinarith [had, hbsq]

theorem odd_source_det_pos_of_c4_upper
    (hc4 : nativeC 4 ≤ (4/10^9:ℝ)) :
    0 < (coefficientBlock (sourceKernel nativeC true) 2).det :=
  lt_trans (by norm_num) (odd_source_det_margin_of_c4_upper hc4)

theorem odd_source_det_pos_of_head_box
    (hbox : ‖regroupedHead64 4 - (oddHeadFourthCenter : ℂ)‖ ≤ (1/10^12:ℝ)) :
    0 < (coefficientBlock (sourceKernel nativeC true) 2).det :=
  odd_source_det_pos_of_c4_upper (native_c4_upper_of_head_box hbox)

/-- A one-sided head bound suffices; the original tail remains in the bound. -/
theorem native_c4_upper_of_head_upper
    (hhead : (regroupedHead64 4).re ≤ (3999/10^12:ℝ)) :
    nativeC 4 ≤ (4/10^9:ℝ) := by
  have hs := congrArg Complex.re (regrouped_source 4)
  have ht := (Complex.abs_re_le_norm (regroupedTail64 4)).trans odd_tail_four_bound
  have htu := (abs_le.mp ht).2
  simp only [Complex.add_re, Complex.ofReal_re] at hs
  norm_num at hs htu hhead ⊢
  linarith

theorem odd_source_det_pos_of_head_upper
    (hhead : (regroupedHead64 4).re ≤ (3999/10^12:ℝ)) :
    0 < (coefficientBlock (sourceKernel nativeC true) 2).det :=
  odd_source_det_pos_of_c4_upper (native_c4_upper_of_head_upper hhead)

theorem odd_c4_ceiling_of_head_upper
    (hhead : (regroupedHead64 4).re ≤ (3999/10^12:ℝ)) :
    nativeC 4 < oddPrefixC4Ceiling nativeC :=
  (odd_prefix_det_pos_iff_c4 nativeC native_source_c0_positive_from_boxes
    third_odd_prefix_first_entry_pos_from_c3).mp (odd_source_det_pos_of_head_upper hhead)

theorem odd_prefix_isUnit_of_head_upper
    (hhead : (regroupedHead64 4).re ≤ (3999/10^12:ℝ)) :
    IsUnit (sourceMomentMatrix nativeH 1 2) :=
  third_odd_prefix_isUnit_of_c4_source_bound (odd_c4_ceiling_of_head_upper hhead)

theorem third_odd_gate_of_head_upper
    (hhead : (regroupedHead64 4).re ≤ (3999/10^12:ℝ)) :
    0 < sourceMomentSchur nativeH 1 2 ↔
      nativeC 6 < oddSourceCeiling nativeC / (6*nativeC 0) :=
  third_odd_gate_of_c4_source_bound (odd_c4_ceiling_of_head_upper hhead)

/-- Both independent arguments and all four terms of the literal original split. -/
theorem odd_original_four_terms (x y : Fin 2 → ℝ) :
    coefficientPair (fun n => (nativeC n:ℂ)) (fun n => (nativeC n:ℂ)) true 2 x y =
      coefficientPair regroupedHead64 regroupedHead64 true 2 x y +
      coefficientPair regroupedHead64 regroupedTail64 true 2 x y +
      coefficientPair regroupedTail64 regroupedHead64 true 2 x y +
      coefficientPair regroupedTail64 regroupedTail64 true 2 x y := by
  have he : regroupedHead64 + regroupedTail64 = (fun n => (nativeC n:ℂ)) := by
    funext n
    exact regrouped_source n
  rw [← he]
  exact coefficientPair_four_terms _ _ _ _ _ _ _ _

#print axioms odd_tail_four_bound
#print axioms native_c4_upper_of_head_box
#print axioms odd_source_det_margin_of_c4_upper
#print axioms odd_source_det_pos_of_c4_upper
#print axioms odd_original_four_terms
#print axioms odd_c4_ceiling_of_head_upper
#print axioms third_odd_gate_of_head_upper

end
end CarryOddHeadSource
