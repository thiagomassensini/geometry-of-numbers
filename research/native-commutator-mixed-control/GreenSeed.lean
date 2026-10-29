import MixedReduction

namespace CarryCommutatorControl
open CarrySelfAdjointOperator CarryNativeTfvd NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem seed_is_native_zero_jet (k : ℕ) :
    physicalCompletedFiniteSource k (Finsupp.single 0 1) = projectiveChiralDifferenceJet k 0 := by
  rw [physicalCompletedFiniteSource_original]
  simp [projectiveChiralDifferenceJet, completedGreenForwardWeight]

/-- First finite test, with the outgoing neighbor retained exactly. -/
theorem commutator_seed (eta : ℝ) (w : ℕ → ℂ) :
    completionCommutator eta w (Finsupp.single 0 1) =
      Finsupp.single 1 ((eta : ℂ) * (w 0-w 1)) := by
  ext j
  rcases j with _ | _ | j
  · simp [completion_commutator_zero]
  · simp [completion_commutator_succ]
  · simp [completion_commutator_succ]

theorem physical_commutator_seed (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (k : ℕ) :
    (completedSourceParts eta h0 h1 k (Finsupp.single 0 1) 2).1 =
      ((Real.sqrt ((k : ℝ)+1) : ℂ) * (eta : ℂ) *
        (incidentWeight k 0-incidentWeight k 1)) •
          physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature 1) := by
  change (Real.sqrt ((k : ℝ)+1) : ℂ) • physicalGreenOperator eta h0.le h1
    (physicalCauchySynthesis (completionCommutator eta (incidentWeight k) (Finsupp.single 0 1))) = _
  rw [commutator_seed]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_single, map_smul, smul_smul]
  congr 1
  ring

theorem physical_resolvent_selfAdjoint (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta < 1) :
    IsSelfAdjoint (physicalGreenResolvent eta h0 h1) := by
  apply intervalMultiplier_isSelfAdjoint
  intro u
  simp [physicalResolventCoefficient]

/-- The ORIGINAL physical Green cross is a strictly positive norm, not a fitted constant. -/
theorem green_seed_cross (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta < 1) :
    inner ℂ (completedNativeChiralCauchyFeature 0)
      (physicalGreenOperator eta h0 h1 (completedNativeChiralCauchyFeature 1)) =
      (eta : ℂ) * ((‖physicalGreenResolvent eta h0 h1
        (completedNativeChiralCauchyFeature 1)‖ ^ 2 : ℝ) : ℂ) := by
  have hM := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp physicalRadialAdvance_isSelfAdjoint
  have hR := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (physical_resolvent_selfAdjoint eta h0 h1)
  unfold physicalGreenOperator
  rw [smul_apply, mul_apply_eq_comp, inner_smul_right]
  have hm := hM (completedNativeChiralCauchyFeature 0)
    (((physicalGreenResolvent eta h0 h1)^2) (completedNativeChiralCauchyFeature 1))
  change inner ℂ (physicalRadialAdvance (completedNativeChiralCauchyFeature 0)) _ =
    inner ℂ (completedNativeChiralCauchyFeature 0) _ at hm
  rw [physicalRadialAdvance_feature] at hm
  have hr := hR (completedNativeChiralCauchyFeature 1)
    (physicalGreenResolvent eta h0 h1 (completedNativeChiralCauchyFeature 1))
  change inner ℂ (physicalGreenResolvent eta h0 h1 (completedNativeChiralCauchyFeature 1)) _ =
    inner ℂ (completedNativeChiralCauchyFeature 1) _ at hr
  congr 1
  calc
    _ = inner ℂ (completedNativeChiralCauchyFeature 1)
        (((physicalGreenResolvent eta h0 h1)^2) (completedNativeChiralCauchyFeature 1)) := hm.symm
    _ = inner ℂ (physicalGreenResolvent eta h0 h1 (completedNativeChiralCauchyFeature 1))
        (physicalGreenResolvent eta h0 h1 (completedNativeChiralCauchyFeature 1)) := hr.symm
    _ = _ := by rw [inner_self_eq_norm_sq_to_K]; norm_cast

theorem green_seed_cross_re_pos (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    0 < (inner ℂ (completedNativeChiralCauchyFeature 0)
      (physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature 1))).re := by
  have hp : completedNativeChiralCauchyFeature 1 ≠ 0 := by
    intro hz
    have h := inner_completedNativeChiralCauchyFeature 1 1
    rw [hz] at h
    norm_num at h
  have hr : physicalGreenResolvent eta h0.le h1 (completedNativeChiralCauchyFeature 1) ≠ 0 := by
    intro hz
    have h := congrArg (fun T : CanonicalCompletedNativeChiralCauchyCarrier →L[ℂ]
        CanonicalCompletedNativeChiralCauchyCarrier => T (completedNativeChiralCauchyFeature 1))
      (physicalGreenResolvent_right_inverse eta h0.le h1)
    change (1-(eta : ℂ) • physicalRadialAdvance)
      (physicalGreenResolvent eta h0.le h1 (completedNativeChiralCauchyFeature 1)) =
        completedNativeChiralCauchyFeature 1 at h
    rw [hz, map_zero] at h
    exact hp h.symm
  rw [green_seed_cross]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos h0 (sq_pos_of_pos (norm_pos_iff.mpr hr))

/-- The observable is the SAME complete mixed source correction, not its norm. -/
def seedMixed (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (k : ℕ) : ℝ :=
  (canonicalCompletedNativeProjectiveChiralForm
      (completedSourceParts eta h0 h1 k (Finsupp.single 0 1) 2)
      (physicalCompletedFiniteSource k (Finsupp.single 0 1)) +
   canonicalCompletedNativeProjectiveChiralForm
      (physicalCompletedFiniteSource k (Finsupp.single 0 1))
      (completedSourceParts eta h0 h1 k (Finsupp.single 0 1) 2)).re

private theorem symmetric_inner_re (u v : CanonicalCompletedNativeChiralCauchyCarrier) :
    ((2 : ℂ)⁻¹ * (inner ℂ v u + inner ℂ u v)).re = (inner ℂ u v).re := by
  have h : (inner ℂ v u).re = (inner ℂ u v).re := by
    exact_mod_cast inner_re_symm (𝕜 := ℂ) v u
  norm_num [Complex.mul_re, Complex.add_re, h]
  ring

theorem seed_mixed_exact (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (k : ℕ)
    (hd : ∀ j : ℕ, j < 2 → incidentWeight k j-returnedWeight k j=chiralDifference) :
    seedMixed eta h0 h1 k =
      ((((k : ℝ)+1) : ℂ) * (eta : ℂ) * conj chiralDifference *
        (incidentWeight k 0-incidentWeight k 1) *
        inner ℂ (completedNativeChiralCauchyFeature 0)
          (physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature 1))).re := by
  have hc : (Finsupp.single 0 (1 : ℂ)).support ⊆ Finset.range 1 := by simp
  unfold seedMixed
  rw [completed_commutator_mixed_pairing eta h0 h1 k _ _ hc hc hd, symmetric_inner_re,
    physical_commutator_seed]
  simp only [physicalCauchySynthesis, Finsupp.linearCombination_single, one_smul]
  have hs : (Real.sqrt ((k : ℝ)+1) : ℂ)^2 = (((k : ℝ)+1) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  simp only [inner_smul_left, inner_smul_right, map_mul]
  have hconj : conj (Real.sqrt ((k : ℝ)+1) : ℂ) = (Real.sqrt ((k : ℝ)+1) : ℂ) := by simp
  rw [hconj]
  congr 1
  push_cast at hs ⊢
  linear_combination (eta : ℂ) * conj chiralDifference * (incidentWeight k 0-incidentWeight k 1) *
    inner ℂ (completedNativeChiralCauchyFeature 0)
      (physicalGreenOperator eta h0.le h1 (completedNativeChiralCauchyFeature 1)) * hs

end
end CarryCommutatorControl
