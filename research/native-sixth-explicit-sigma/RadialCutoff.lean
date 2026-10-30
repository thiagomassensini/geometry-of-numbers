import CriticalCoefficient
import RadialPairs
import TwelveBridge

namespace CarrySixthExplicit
open CarrySelfAdjointOperator CarrySixthRelative CarryDirectAnchor CarryVariationalSchur
open CarryCriticalSource CarrySixthOdd CarrySummableRadial CarryExplicitBudget CarryOddEnergy
open CarryBoundaryReconstruction CarryCriticalTfvd
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000

def explicitRadialIndex : ℕ := 10^28-1

theorem explicit_radial_grid_cutoff : oddGridCutoff twelveOrders ≤ explicitRadialIndex := by
  have hcut : oddGridCutoff twelveOrders = 48 := by decide +kernel
  rw [hcut]
  norm_num [explicitRadialIndex]

theorem explicit_radial_step (k : ℕ) (hk : explicitRadialIndex ≤ k) :
    radialFourSourceStep k ≤ 1/(10:ℝ)^28 := by
  have hn : (10:ℝ)^28 ≤ (k:ℝ)+1 := by
    exact_mod_cast (show (10:ℕ)^28≤k+1 by unfold explicitRadialIndex at hk; omega)
  unfold radialFourSourceStep
  rw [one_div]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hn

theorem trial_family_budget_bound : familyConstant twelveOrders twelveCoeff ≤ 36*(10:ℝ)^12 := by
  have h := finite_family_budget_bound twelveOrders twelveCoeff 1 ((10:ℝ)^12) (by norm_num)
    twelve_trial_coefficient_bound
    (by intro r hr s hs; exact twelve_pair_constants_bounded r s hr hs)
  norm_num [twelveOrders] at h ⊢
  exact h

theorem critical_family_budget_bound :
    familyConstant (Finset.range 6) (coefficientFromFin (criticalFin 5)) ≤ 144*(10:ℝ)^12 := by
  have h := finite_family_budget_bound twelveOrders (coefficientFromFin (criticalFin 5)) 2 ((10:ℝ)^12)
    (by norm_num)
    (by
      intro r hr
      have hr' : r<6 := Finset.mem_range.mp hr
      simpa [coefficientFromFin,hr'] using critical_coefficient_bound ⟨r,hr'⟩)
    (by intro r hr s hs; exact twelve_pair_constants_bounded r s hr hs)
  norm_num [twelveOrders] at h ⊢
  exact h

theorem trial_error_identity (k : ℕ) :
    physicalFiniteError 6 (trialFin 5 twelveSolve) k =
      (radialFourSourceStep k)^2*familyConstant twelveOrders twelveCoeff := by
  unfold physicalFiniteError familyConstant twelveOrders
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [twelve_trialFin_coeff i hi,twelve_trialFin_coeff j hj]

theorem trial_error_after_cutoff (k : ℕ) (hk : explicitRadialIndex ≤ k) :
    physicalFiniteError 6 (trialFin 5 twelveSolve) k ≤ 1/(10:ℝ)^42 := by
  rw [trial_error_identity]
  have hb := trial_family_budget_bound
  have hp := radial_step_positive k
  have hs := explicit_radial_step k hk
  have hs2 : (radialFourSourceStep k)^2 ≤ (1/(10:ℝ)^28)^2 := by nlinarith [sq_nonneg (radialFourSourceStep k)]
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg (radialFourSourceStep k))
  have hn := mul_le_mul_of_nonneg_left hs2 (show (0:ℝ)≤36*(10:ℝ)^12 by positivity)
  norm_num at *
  nlinarith

theorem critical_error_after_cutoff (k : ℕ) (hk : explicitRadialIndex ≤ k) :
    physicalFiniteError 6 (criticalFin 5) k ≤ 2/(10:ℝ)^42 := by
  have hb := critical_family_budget_bound
  have hp := radial_step_positive k
  have hs := explicit_radial_step k hk
  have hs2 : (radialFourSourceStep k)^2 ≤ (1/(10:ℝ)^28)^2 := by nlinarith [sq_nonneg (radialFourSourceStep k)]
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg (radialFourSourceStep k))
  have hn := mul_le_mul_of_nonneg_left hs2 (show (0:ℝ)≤144*(10:ℝ)^12 by positivity)
  unfold physicalFiniteError
  norm_num at *
  nlinarith

theorem trial_source_lower_after_cutoff (k : ℕ) (hk : explicitRadialIndex ≤ k) :
    9/(10:ℝ)^37 < finiteSourceEnergy 6 (trialFin 5 twelveSolve) k := by
  have hcut : oddGridCutoff (Finset.range 6) ≤ k := by
    exact explicit_radial_grid_cutoff.trans hk
  have he := finite_source_error 6 (trialFin 5 twelveSolve) k hcut
  rw [twelve_trial_form_identity] at he
  have hl := (abs_le.mp he).1
  have hh := twelve_trial_form_lower
  have hb := trial_error_after_cutoff k hk
  have hn : (9/(10:ℝ)^37)+(1/(10:ℝ)^42) < 1/(10:ℝ)^36 := by norm_num
  linarith

theorem relative_budget_after_cutoff (k : ℕ) (hk : explicitRadialIndex ≤ k) :
    (sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve ⬝ᵥ
      ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 5)⁻¹ *ᵥ
        sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve)) +
      physicalFiniteError 6 (trialFin 5 twelveSolve) k +
      2*physicalFiniteError 6 (criticalFin 5) k <
        (1/50:ℝ)*finiteSourceEnergy 6 (trialFin 5 twelveSolve) k := by
  have hr := original_inverse_correction_upper
  have ht := trial_error_after_cutoff k hk
  have hc := critical_error_after_cutoff k hk
  have hl := trial_source_lower_after_cutoff k hk
  have hn : (1/(10:ℝ)^38)+5*(1/(10:ℝ)^42) < (1/50:ℝ)*(9/(10:ℝ)^37) := by norm_num
  nlinarith

theorem critical_anchor_after_cutoff (k : ℕ) (hk : explicitRadialIndex ≤ k) :
    physicalFiniteError 6 (criticalFin 5) k < finiteSourceEnergy 6 (criticalFin 5) k := by
  have hcut : oddGridCutoff (Finset.range 6) ≤ k := explicit_radial_grid_cutoff.trans hk
  apply finite_odd_critical_anchor_of_relative_budget 5 k twelveSolve (1/50) twelve_old_isUnit hcut (by norm_num)
  · have hl := trial_source_lower_after_cutoff k hk
    have hn : (0:ℝ)<9/(10:ℝ)^37 := by norm_num
    linarith
  · exact (relative_budget_after_cutoff k hk).le

/-- Explicit lower margin for the same complete critical physical source. -/
theorem critical_source_lower_after_cutoff (k : ℕ) (hk : explicitRadialIndex ≤ k) :
    8/(10:ℝ)^37 < finiteSourceEnergy 6 (criticalFin 5) k := by
  have hcut : oddGridCutoff (Finset.range 6) ≤ k := explicit_radial_grid_cutoff.trans hk
  have htransfer := finite_critical_transfer 5 k twelveSolve twelve_old_isUnit hcut
  have hr := original_inverse_correction_upper
  have ht := trial_error_after_cutoff k hk
  have hc := critical_error_after_cutoff k hk
  have hl := trial_source_lower_after_cutoff k hk
  have hn : (8/(10:ℝ)^37)+(1/(10:ℝ)^38)+3*(1/(10:ℝ)^42) < 9/(10:ℝ)^37 := by norm_num
  linarith

theorem critical_anchor_at_cutoff :
    physicalFiniteError 6 (criticalFin 5) explicitRadialIndex <
      finiteSourceEnergy 6 (criticalFin 5) explicitRadialIndex :=
  critical_anchor_after_cutoff _ le_rfl

end
end CarrySixthExplicit
