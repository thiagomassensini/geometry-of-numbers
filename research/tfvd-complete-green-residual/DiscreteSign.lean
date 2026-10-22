import ObliqueTfvd

/-! Test discrete integration by parts in the unchanged critical metric.
The weighted stencil is not the unweighted discrete Laplacian. Its exact
symmetric part contains a negative bulk term as well as the difference norm. -/
namespace CarryCompleteTfvd
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.RealCarry
open scoped BigOperators InnerProductSpace lp ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem vertical_shift_norm (x : CarryVerticalL2) :
    ‖carryVerticalL2UnilateralShift 1 x‖ = ‖x‖ := by
  have he : carryVerticalL2BackwardShift 1 (carryVerticalL2UnilateralShift 1 x) = x := by
    ext n
    simp only [carryVerticalL2BackwardShift_apply, carryVerticalL2UnilateralShift_apply]
    simp
  apply le_antisymm
  · simpa only [one_mul] using (carryVerticalL2UnilateralShift 1).le_of_opNorm_le
      (carryVerticalL2UnilateralShift_norm_le_one 1) x
  · have h := carryVerticalL2BackwardShiftLinear_norm_le 1 (carryVerticalL2UnilateralShift 1 x)
    change ‖carryVerticalL2BackwardShift 1 (carryVerticalL2UnilateralShift 1 x)‖ ≤ _ at h
    rw [he] at h
    exact h

theorem weighted_core_energy (eta : ℝ) (x : CarryVerticalL2) :
    -inner ℝ x (carryWeightedVerticalCenteredBracketCore eta x) =
      ((eta+eta⁻¹)/2)*‖carryVerticalL2UnilateralShift 1 x-x‖^2 -
        (eta+eta⁻¹-2)*‖x‖^2 := by
  have ha : inner ℝ x (carryVerticalL2BackwardShift 1 x) =
      inner ℝ x (carryVerticalL2UnilateralShift 1 x) := by
    have hh := ContinuousLinearMap.adjoint_inner_right (carryVerticalL2BackwardShift 1) x x
    change inner ℝ x (carryVerticalL2UnilateralShift 1 x) =
      inner ℝ (carryVerticalL2BackwardShift 1 x) x at hh
    calc
      _ = inner ℝ (carryVerticalL2BackwardShift 1 x) x := real_inner_comm _ _
      _ = _ := hh.symm
  have hd := norm_sub_sq_real (carryVerticalL2UnilateralShift 1 x) x
  rw [vertical_shift_norm, real_inner_comm] at hd
  simp only [carryWeightedVerticalCenteredBracketCore, add_apply,
    sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_right, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [ha]
  rw [hd]
  ring

/-- A genuine finite-support vertical state, with BOTH trace coordinates zero. -/
def plateauEighteen : CarryVerticalL2 :=
  ∑ k ∈ Finset.range 18, lp.single 2 (k+2) (1:ℝ)

theorem plateau_apply (n : ℕ) :
    plateauEighteen n = if 2 ≤ n ∧ n < 20 then 1 else 0 := by
  change carryVerticalL2Eval n (∑ k ∈ Finset.range 18, lp.single 2 (k+2) (1:ℝ)) = _
  rw [map_sum]
  simp only [carryVerticalL2Eval_apply, lp.single_apply, Pi.single_apply]
  by_cases hn : 2 ≤ n ∧ n < 20
  · rw [if_pos hn, Finset.sum_eq_single (n-2)]
    · simp [show n-2+2 = n by omega]
    · intro k _ hk
      simp [show n ≠ k+2 by omega]
    · simp [show n-2 < 18 by omega]
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k < 18 := Finset.mem_range.mp hk
    simp [show n ≠ k+2 by omega]

theorem plateau_trace_zero (eta : ℝ) :
    carryWeightedVerticalTrace eta plateauEighteen = 0 := by
  simp [carryWeightedVerticalTrace_apply, plateau_apply]

theorem plateau_curvature_energy (eta : ℝ) :
    inner ℝ plateauEighteen (carryWeightedVerticalCenteredBracket eta plateauEighteen) =
      17*(eta+eta⁻¹)-36 := by
  have hb (k : ℕ) : carryWeightedVerticalCenteredBracket eta plateauEighteen (k+2) =
      eta⁻¹*plateauEighteen (k+3)-2*plateauEighteen (k+2)+eta*plateauEighteen (k+1) := by
    simpa only [Nat.add_assoc] using carryWeightedVerticalCenteredBracket_succ eta plateauEighteen (k+1)
  change inner ℝ (∑ k ∈ Finset.range 18, lp.single 2 (k+2) (1:ℝ))
    (carryWeightedVerticalCenteredBracket eta plateauEighteen) = _
  rw [sum_inner]
  simp only [lp.inner_single_left, Real.inner_apply, one_mul]
  simp_rw [hb, plateau_apply]
  norm_num [Finset.sum_range_succ]
  ring

/-- The natural negated second-difference candidate fails even on zero-trace
finite states at eta_2; this is not a negative CANONICAL moment witness. -/
theorem critical_plateau_negative_laplacian :
    -inner ℝ plateauEighteen
      (carryWeightedVerticalCenteredBracket (criticalVerticalAmplitudeRatio 2 (by norm_num))
        plateauEighteen) < 0 := by
  let eta := criticalVerticalAmplitudeRatio 2 (by norm_num)
  have hp : 0 < eta := criticalVerticalAmplitudeRatio_pos 2 _
  have hsq : eta^(2:ℕ) = (1/2:ℝ) := by
    dsimp [eta]
    rw [criticalVerticalAmplitudeRatio_eq_rpow]
    change ((2:ℝ)^(-(1:ℝ)/2))^(2:ℕ) = _
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hi : eta⁻¹ = 2*eta := by
    apply (mul_left_cancel₀ hp.ne')
    rw [mul_inv_cancel₀ hp.ne']
    nlinarith [hsq]
  rw [plateau_curvature_energy]
  change -(17*(eta+eta⁻¹)-36) < 0
  rw [hi]
  have hh : (12/17:ℝ) < eta := by nlinarith [sq_nonneg (eta-(12/17:ℝ))]
  linarith

/-- Exact head term for the centered operator; no boundary is suppressed. -/
theorem weighted_centered_energy (eta : ℝ) (x : CarryVerticalL2) :
    -inner ℝ x (carryWeightedVerticalCenteredBracket eta x) =
      ((eta+eta⁻¹)/2)*‖carryVerticalL2UnilateralShift 1 x-x‖^2 -
        (eta+eta⁻¹-2)*‖x‖^2 + x 0*(eta⁻¹*x 1-2*x 0) := by
  have he : carryWeightedVerticalCenteredBracket eta x =
      carryWeightedVerticalCenteredBracketCore eta x -
        (carryWeightedVerticalCenteredBracketCore eta x 0) • lp.single 2 0 (1:ℝ) := rfl
  rw [he, inner_sub_right, inner_smul_right, lp.inner_single_right]
  rw [Real.inner_apply, mul_one]
  have hv : carryWeightedVerticalCenteredBracketCore eta x 0 = eta⁻¹*x 1-2*x 0 := by
    simp
  rw [hv]
  linear_combination weighted_core_energy eta x

theorem weighted_negative_bulk (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    0 < eta+eta⁻¹-2 := by
  have he : eta+eta⁻¹-2 = (1-eta)^2/eta := by field_simp; ring
  rw [he]
  exact div_pos (sq_pos_of_pos (sub_pos.mpr h1)) h0

/-- Trace-zero data need not give a nonnegative negated-curvature form. -/
theorem critical_no_tracezero_laplacian_positive :
    ¬ ∀ x : CarryVerticalL2,
      carryWeightedVerticalTrace (criticalVerticalAmplitudeRatio 2 (by norm_num)) x = 0 →
      0 ≤ -inner ℝ x (carryWeightedVerticalCenteredBracket
        (criticalVerticalAmplitudeRatio 2 (by norm_num)) x) := by
  intro h
  exact (not_le.mpr critical_plateau_negative_laplacian)
    (h plateauEighteen (plateau_trace_zero _))

end
end CarryCompleteTfvd
