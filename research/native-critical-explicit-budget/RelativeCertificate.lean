import NumericCutoff
import RelativeGate

namespace CarryExplicitBudget
open CarrySelfAdjointOperator CarryDirectAnchor CarryVariationalSchur CarrySummableRadial
open CarryBoundaryReconstruction CarryOddEnergy
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- The inverse-residual correction and BOTH radial budgets consume less
than one percent of the same complete physical trial energy. -/
theorem ten_relative_budget_after_numeric_cutoff (k : ℕ) (hk : tenAnchorIndex ≤ k) :
    (sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 4 trialSolve ⬝ᵥ
      ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 4)⁻¹ *ᵥ
        sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 4 trialSolve)) +
    physicalFiniteError 5 (trialFin 4 trialSolve) k +
    2*physicalFiniteError 5 (criticalFin 4) k <
      (1/100:ℝ)*finiteSourceEnergy 5 (trialFin 4 trialSolve) k := by
  have hR := ten_original_inverse_correction_upper
  change sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 4 trialSolve ⬝ᵥ
    ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 4)⁻¹ *ᵥ
      sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 4 trialSolve) < 5/(10:ℝ)^35 at hR
  have hsource := ten_trial_source_lower_after_anchor k hk
  have htrial := ten_trial_tail_budget_after_anchor k hk
  have hcrit := critical_error_at_numeric_cutoff k hk
  rw [trial_fin_source_equal,trial_fin_error_equal]
  have ht : (radialFourSourceStep k)^2*familyConstant tenOrders trialCoefficient ≤ 25/(10:ℝ)^34 := by
    simpa only [mul_comm] using htrial
  have hn : (5/(10:ℝ)^35)+(25/(10:ℝ)^34)+2*(1/(10:ℝ)^32) <
      (1/100:ℝ)*(6/(10:ℝ)^30) := by norm_num
  nlinarith

/-- A check that the general criterion indeed consumes the concrete
relative certificate and returns the original critical physical anchor. -/
theorem ten_anchor_via_relative_budget (k : ℕ) (hk : tenAnchorIndex ≤ k) :
    physicalFiniteError 5 (criticalFin 4) k < finiteSourceEnergy 5 (criticalFin 4) k := by
  apply finite_odd_critical_anchor_of_relative_budget 4 k trialSolve (1/100) ten_old_block_isUnit
    (ten_anchor_cutoff.trans hk) (by norm_num)
  · rw [trial_fin_source_equal]
    have h := ten_trial_source_lower_after_anchor k hk
    have hh : (0:ℝ)<6/(10:ℝ)^30 := by norm_num
    linarith
  · exact (ten_relative_budget_after_numeric_cutoff k hk).le

end
end CarryExplicitBudget
