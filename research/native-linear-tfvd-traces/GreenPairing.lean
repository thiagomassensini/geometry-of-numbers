import PhysicalNumerator
import GreenSeed

namespace CarryLinearTfvd
open CarrySelfAdjointOperator NativeCauchyPorts NativeLaguerre
open CarryNativeTfvd CarryCriticalTfvd CarryCurvatureGreen CarryCommutatorControl
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- Green is transported as a full mixed pairing; M stays on its original
physical domain and is never inverted. -/
theorem green_inner_right_numerator (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ f (physicalGreenOperator eta h0.le h1 g) =
      (eta : ℂ)*inner ℂ (physicalGreenResolvent eta h0.le h1 f)
        (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance g)) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (physical_resolvent_selfAdjoint eta h0.le h1)
  have hh := hs f (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance g))
  change inner ℂ (physicalGreenResolvent eta h0.le h1 f)
    (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance g)) =
      inner ℂ f (physicalGreenResolvent eta h0.le h1
        (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance g))) at hh
  simp only [resolvent_advance eta h0 h1] at hh
  unfold physicalGreenOperator
  rw [smul_apply, mul_apply_eq_comp, inner_smul_right]
  change (eta : ℂ)*inner ℂ f (physicalRadialAdvance
    (physicalGreenResolvent eta h0.le h1 (physicalGreenResolvent eta h0.le h1 g))) = _
  rw [← hh, resolvent_advance eta h0 h1]

theorem double_advance_pairing (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (f g : PhysicalSpace) :
    inner ℂ (physicalGreenResolvent eta h0.le h1 f)
      (physicalGreenResolvent eta h0.le h1
        (physicalRadialAdvance (physicalRadialAdvance g))) =
      inner ℂ (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance f))
        (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance g)) := by
  simp only [resolvent_advance eta h0 h1]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    physicalRadialAdvance_isSelfAdjoint _ _).symm

/-- Arbitrary independent complex inputs. BOTH trace coefficients remain in
the mixed boundary term, before taking real parts or setting the inputs equal. -/
theorem green_linear_polarized_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (c d : ℕ →₀ ℂ) :
    inner ℂ (physicalCauchySynthesis c) (physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) d))) =
      inner ℂ (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))
        (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis d)) -
      inner ℂ (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))
        (physicalGreenResolvent eta h0.le h1 (physicalTrace d)) -
      (eta : ℂ)^2 * inner ℂ
        (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (physicalCauchySynthesis c)))
        (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (physicalCauchySynthesis d))) := by
  rw [green_inner_right_numerator eta h0 h1, physical_linear_numerator]
  simp only [map_sub, map_smul, inner_sub_right, inner_smul_right]
  rw [double_advance_pairing eta h0 h1]
  have he : (eta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  field_simp [he]

theorem green_linear_diagonal_factor (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (c : ℕ →₀ ℂ) :
    (inner ℂ (physicalCauchySynthesis c) (physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) c)))).re =
      ‖physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c)‖^2 -
      (inner ℂ (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))
        (physicalGreenResolvent eta h0.le h1 (physicalTrace c))).re -
      eta^2*‖physicalGreenResolvent eta h0.le h1
        (physicalRadialAdvance (physicalCauchySynthesis c))‖^2 := by
  rw [green_linear_polarized_factor eta h0 h1 c c,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  have hRe (r : ℝ) : ((r : ℂ)^2).re=r^2 := by simp [pow_two,Complex.mul_re]
  have hIm (r : ℝ) : ((r : ℂ)^2).im=0 := by simp [pow_two,Complex.mul_im]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  norm_num [Complex.mul_re, Complex.sub_re, hRe, hIm]

theorem advance_contracts (f : PhysicalSpace) : ‖physicalRadialAdvance f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖physicalRadialAdvance‖*‖f‖ := physicalRadialAdvance.le_opNorm f
    _ ≤ 1*‖f‖ := mul_le_mul_of_nonneg_right physicalRadialAdvance_norm_le_one (norm_nonneg _)
    _ = _ := one_mul _

/-- A geometric lower bound with the ACTUAL two-trace cross still present. -/
theorem green_linear_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (c : ℕ →₀ ℂ) :
    (1-eta^2)*‖physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c)‖^2 -
      (inner ℂ (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))
        (physicalGreenResolvent eta h0.le h1 (physicalTrace c))).re ≤
    (inner ℂ (physicalCauchySynthesis c) (physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) c)))).re := by
  have hh := advance_contracts (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))
  rw [← resolvent_advance eta h0 h1] at hh
  have hs : ‖physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (physicalCauchySynthesis c))‖^2 ≤
      ‖physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c)‖^2 := by
    nlinarith [norm_nonneg (physicalGreenResolvent eta h0.le h1 (physicalRadialAdvance (physicalCauchySynthesis c))),
      norm_nonneg (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg eta)
  rw [green_linear_diagonal_factor eta h0 h1]
  nlinarith

/-- This subspace is fixed by vanishing of the two original traces, not chosen
by the desired moment signs. Native difference stencils need not lie in it. -/
theorem green_linear_zero_traces_lower (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (c : ℕ →₀ ℂ) (hc0 : c 0=0) (hc1 : c 1=0) :
    (1-eta^2)*‖physicalCauchySynthesis c‖^2 ≤
    (inner ℂ (physicalCauchySynthesis c) (physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) c)))).re := by
  have hl := green_linear_lower eta h0 h1 c
  have hn := resolvent_norm_lower eta h0.le h1 (physicalCauchySynthesis c)
  have hs : ‖physicalCauchySynthesis c‖^2 ≤
      ‖physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c)‖^2 := by
    nlinarith [norm_nonneg (physicalCauchySynthesis c),
      norm_nonneg (physicalGreenResolvent eta h0.le h1 (physicalCauchySynthesis c))]
  have ht : physicalTrace c=0 := by simp [physicalTrace,hc0,hc1]
  rw [ht, map_zero, inner_zero_right, Complex.zero_re, sub_zero] at hl
  have hm := mul_le_mul_of_nonneg_left hs (by nlinarith : 0≤1-eta^2)
  exact hm.trans hl

theorem green_linear_zero_traces_pos (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (c : ℕ →₀ ℂ) (hc0 : c 0=0) (hc1 : c 1=0) (hc : physicalCauchySynthesis c ≠ 0) :
    0 < (inner ℂ (physicalCauchySynthesis c) (physicalGreenOperator eta h0.le h1
      (physicalCauchySynthesis (completionCommutator eta (monomialWeight 1) c)))).re := by
  apply lt_of_lt_of_le _ (green_linear_zero_traces_lower eta h0 h1 c hc0 hc1)
  exact mul_pos (by nlinarith : 0<1-eta^2) (sq_pos_of_pos (norm_pos_iff.mpr hc))

/-- Exact counterexample to discarding the traces or asserting a positive
linear commutator on ALL sources: the original seed gives a negative value. -/
theorem green_linear_seed_negative (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (inner ℂ (physicalCauchySynthesis (Finsupp.single 0 1))
      (physicalGreenOperator eta h0.le h1 (physicalCauchySynthesis
        (completionCommutator eta (monomialWeight 1) (Finsupp.single 0 1))))).re < 0 := by
  have hs : completionCommutator eta (monomialWeight 1) (Finsupp.single 0 1) =
      Finsupp.single 1 (-(eta : ℂ)) := by
    ext j
    rcases j with _ | _ | j
    all_goals simp [completion_commutator_zero, linear_commutator_succ]
  have hp := green_seed_cross_re_pos eta h0 h1
  rw [hs]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_single, one_smul,
    map_smul, inner_smul_right]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im]
  nlinarith

end
end CarryLinearTfvd
