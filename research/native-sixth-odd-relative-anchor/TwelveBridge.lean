import TwelveCorrection
import RelativeGate

namespace CarrySixthRelative
open CarrySelfAdjointOperator CarryDirectAnchor CarryIntegralCertificate CarryVariationalSchur
open CarryCriticalSource CarrySummableRadial CarryOddEnergy CarryBoundaryReconstruction CarryExplicitBudget
open Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem twelve_trial_form_identity :
    sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment 1 6 (trialFin 5 twelveSolve) =
      oddCanonicalForm twelveOrders twelveCoeff := by
  rw [← finite_odd_form_eq_quadratic]
  unfold oddCanonicalForm twelveOrders
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [twelve_trialFin_coeff i hi,twelve_trialFin_coeff j hj]

theorem twelve_trial_physical_eventually_lower :
    ∀ᶠ k : ℕ in atTop, (9/(10:ℝ)^37) < finiteSourceEnergy 6 (trialFin 5 twelveSolve) k := by
  have ht := family_budget_tendsto_zero (Finset.range 6) (coefficientFromFin (trialFin 5 twelveSolve))
  have hsmall : ∀ᶠ k : ℕ in atTop, physicalFiniteError 6 (trialFin 5 twelveSolve) k < 1/(10:ℝ)^40 := by
    have he := Filter.Tendsto.eventually_lt ht tendsto_const_nhds (by norm_num : (0:ℝ)<1/(10:ℝ)^40)
    filter_upwards [he] with k hk
    simpa only [physicalFiniteError,mul_comm] using hk
  filter_upwards [hsmall,eventually_ge_atTop (oddGridCutoff (Finset.range 6))] with k hs hk
  have he := finite_source_error 6 (trialFin 5 twelveSolve) k hk
  rw [twelve_trial_form_identity] at he
  have hq := twelve_trial_form_lower
  have hl := (abs_le.mp he).1
  have hn : (9/(10:ℝ)^37)+(1/(10:ℝ)^40) < 1/(10:ℝ)^36 := by norm_num
  linarith

theorem twelve_relative_budget_eventually : ∀ᶠ k : ℕ in atTop,
    (sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve ⬝ᵥ
      ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 5)⁻¹ *ᵥ
        sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve)) +
      physicalFiniteError 6 (trialFin 5 twelveSolve) k +
      2*physicalFiniteError 6 (criticalFin 5) k <
        (1/50:ℝ)*finiteSourceEnergy 6 (trialFin 5 twelveSolve) k := by
  have ht := family_budget_tendsto_zero (Finset.range 6) (coefficientFromFin (trialFin 5 twelveSolve))
  have hc := family_budget_tendsto_zero (Finset.range 6) (coefficientFromFin (criticalFin 5))
  have hsmallt : ∀ᶠ k : ℕ in atTop, physicalFiniteError 6 (trialFin 5 twelveSolve) k < 1/(10:ℝ)^40 := by
    have he := Filter.Tendsto.eventually_lt ht tendsto_const_nhds (by norm_num : (0:ℝ)<1/(10:ℝ)^40)
    filter_upwards [he] with k hk
    simpa only [physicalFiniteError,mul_comm] using hk
  have hsmallc : ∀ᶠ k : ℕ in atTop, physicalFiniteError 6 (criticalFin 5) k < 1/(10:ℝ)^40 := by
    have he := Filter.Tendsto.eventually_lt hc tendsto_const_nhds (by norm_num : (0:ℝ)<1/(10:ℝ)^40)
    filter_upwards [he] with k hk
    simpa only [physicalFiniteError,mul_comm] using hk
  filter_upwards [hsmallt,hsmallc,twelve_trial_physical_eventually_lower] with k hs ht hh
  have hr := original_inverse_correction_upper
  have hn : (1/(10:ℝ)^38)+3*(1/(10:ℝ)^40) < (1/50:ℝ)*(9/(10:ℝ)^37) := by norm_num
  nlinarith

theorem twelve_critical_anchor_eventually : ∀ᶠ k : ℕ in atTop,
    physicalFiniteError 6 (criticalFin 5) k < finiteSourceEnergy 6 (criticalFin 5) k := by
  filter_upwards [twelve_relative_budget_eventually,twelve_trial_physical_eventually_lower,
    eventually_ge_atTop (oddGridCutoff (Finset.range 6))] with k hr ht hk
  apply finite_odd_critical_anchor_of_relative_budget 5 k twelveSolve (1/50) twelve_old_isUnit hk (by norm_num)
  · have hn : (0:ℝ)<9/(10:ℝ)^37 := by norm_num
    linarith
  · exact hr.le

theorem twelve_critical_anchor_exists : ∃ k : ℕ,
    physicalFiniteError 6 (criticalFin 5) k < finiteSourceEnergy 6 (criticalFin 5) k :=
  twelve_critical_anchor_eventually.exists

end
end CarrySixthRelative
