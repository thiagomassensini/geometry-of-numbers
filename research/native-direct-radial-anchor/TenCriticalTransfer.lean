import TenResidualCertificate
import TenTrialEverywhere

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryCriticalSource CarryCriticalRadialMargin CarryIntegralCertificate CarryVariationalSchur
open CarryNativeTfvd CarryCriticalTfvd CarryOddEnergy CarrySummableRadial CarryBoundaryReconstruction
open Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- The four-column old prefix is the already certified old block; it is
independent of the sign of the fifth odd pivot. -/
theorem ten_old_block_isUnit : IsUnit oldMatrix := by
  have h := sourceMatrices_through_four_posDef 1 4 (by norm_num)
  exact h.isUnit

theorem ten_original_inverse_correction_upper :
    oldResidual ⬝ᵥ (oldMatrix⁻¹ *ᵥ oldResidual) < 5/(10:ℝ)^35 := by
  rw [scaled_inverse_residual scaleReal oldMatrix oldResidual scale_ne_zero ten_old_block_isUnit]
  exact scaled_inverse_correction_upper

theorem trial_fin_coeff_on_range (i : ℕ) (hi : i ∈ tenOrders) :
    coefficientFromFin (trialFin 4 trialSolve) i = trialCoefficient i := by
  have hi' : i<5 := Finset.mem_range.mp hi
  interval_cases i <;> norm_num [coefficientFromFin,trialFin,trialSolve,trialCoefficient,Fin.snoc]

theorem trial_fin_source_equal (k : ℕ) :
    finiteSourceEnergy 5 (trialFin 4 trialSolve) k =
      fullEnergy k (finiteOddJetSource tenOrders trialCoefficient k) := by
  unfold finiteSourceEnergy
  congr 1
  unfold finiteOddJetSource tenOrders
  apply Finset.sum_congr rfl
  intro i hi
  rw [trial_fin_coeff_on_range i hi]

theorem trial_fin_error_equal (k : ℕ) :
    physicalFiniteError 5 (trialFin 4 trialSolve) k =
      (radialFourSourceStep k)^2*familyConstant tenOrders trialCoefficient := by
  unfold physicalFiniteError familyConstant tenOrders
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [trial_fin_coeff_on_range i hi,trial_fin_coeff_on_range j hj]

/-- A single scale with a sufficiently small critical-source budget. -/
theorem ten_critical_anchor_of_small (k : ℕ) (hk : tenAnchorIndex ≤ k)
    (hsmallk : physicalFiniteError 5 (criticalFin 4) k < 1/(10:ℝ)^30) :
    physicalFiniteError 5 (criticalFin 4) k < finiteSourceEnergy 5 (criticalFin 4) k := by
  have hsource := ten_trial_source_lower_after_anchor k hk
  have htail := ten_trial_tail_budget_after_anchor k hk
  have hR := ten_original_inverse_correction_upper
  change sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 4 trialSolve ⬝ᵥ
    ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 4)⁻¹ *ᵥ
      sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 4 trialSolve) < 5/(10:ℝ)^35 at hR
  have htail' : (radialFourSourceStep k)^2*familyConstant tenOrders trialCoefficient ≤ 25/(10:ℝ)^34 := by
    simpa only [mul_comm] using htail
  have htransfer := finite_critical_transfer 4 k trialSolve ten_old_block_isUnit
    (ten_anchor_cutoff.trans hk)
  rw [trial_fin_source_equal,trial_fin_error_equal] at htransfer
  have hn : (5/(10:ℝ)^35)+(25/(10:ℝ)^34)+2*(1/(10:ℝ)^30) < 6/(10:ℝ)^30 := by norm_num
  nlinarith

/-- The exact critical source beats its complete radial tail at every
sufficiently late step; no sign of the new Schur is assumed. -/
theorem ten_critical_anchor_eventually :
    ∀ᶠ k : ℕ in atTop,
      physicalFiniteError 5 (criticalFin 4) k < finiteSourceEnergy 5 (criticalFin 4) k := by
  have hbudget := family_budget_tendsto_zero (Finset.range 5) (coefficientFromFin (criticalFin 4))
  have hsmall : ∀ᶠ k : ℕ in atTop, physicalFiniteError 5 (criticalFin 4) k < 1/(10:ℝ)^30 := by
    have he := Filter.Tendsto.eventually_lt hbudget tendsto_const_nhds (by norm_num : (0:ℝ)<1/(10:ℝ)^30)
    filter_upwards [he] with k hk
    simpa only [physicalFiniteError,mul_comm] using hk
  filter_upwards [hsmall,eventually_ge_atTop tenAnchorIndex] with k hsmallk hk
  exact ten_critical_anchor_of_small k hk hsmallk

theorem ten_critical_anchor_exists : ∃ k : ℕ,
    physicalFiniteError 5 (criticalFin 4) k < finiteSourceEnergy 5 (criticalFin 4) k :=
  ten_critical_anchor_eventually.exists

end
end CarryDirectAnchor
