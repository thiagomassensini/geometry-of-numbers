import CriticalCoefficient
import GeneralBudget

namespace CarryExplicitBudget
open CarrySelfAdjointOperator CarryDirectAnchor CarryIntegralCertificate CarryVariationalSchur
open CarryCriticalRadialMargin CarryCriticalSource CarrySummableRadial CarryBoundaryReconstruction
open CarryCriticalTfvd CarryOddEnergy
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Error relative to the rational trial solve is exactly the inverse residual. -/
theorem critical_old_coefficient_identity (i : Fin 4) :
    criticalFin 4 i.castSucc = trialCoefficient i.val - correctionAt i := by
  have h := sourceTrialResidual_inverse_of_isUnit canonicalCompletedNativeLogDerivativeMoment
    1 4 ten_old_block_isUnit trialSolve
  have hi := congrFun h i
  change correctionAt i =
    (oldMatrix⁻¹ *ᵥ sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment 1 4) i - trialSolve i at hi
  simp only [criticalFin,Fin.snoc_castSucc,Pi.neg_apply]
  simp only [trialSolve,oldMatrix] at hi
  linarith

theorem critical_coefficient_bounded (i : Fin 5) : |criticalFin 4 i| ≤ 2 := by
  by_cases hi : i.val < 4
  · let j : Fin 4 := ⟨i.val,hi⟩
    have hindex : j.castSucc=i := by ext; rfl
    rw [← hindex,critical_old_coefficient_identity]
    have ht := ten_trial_coefficient_bounded j.val (by apply Finset.mem_range.mpr; have hj := j.isLt; omega)
    have hr := correction_bounded j
    have habs := abs_sub (trialCoefficient j.val) (correctionAt j)
    linarith
  · have he : i=4 := by ext; omega
    subst i
    norm_num [criticalFin,Fin.snoc]

theorem critical_family_budget_rational : tenCriticalBudget ≤ 25*(2:ℝ)^2*(10:ℝ)^10 := by
  have h := finite_family_budget_bound tenOrders (coefficientFromFin (criticalFin 4)) 2 ((10:ℝ)^10)
    (by norm_num)
    (by
      intro r hr
      have hr' : r<5 := Finset.mem_range.mp hr
      simpa [coefficientFromFin,hr'] using critical_coefficient_bounded ⟨r,hr'⟩)
    (by intro r hr s hs; exact ten_pair_constants_bounded r s hr hs)
  norm_num [tenCriticalBudget,tenOrders] at h ⊢
  exact h

theorem critical_error_at_numeric_cutoff (k : ℕ) (hk : tenAnchorIndex ≤ k) :
    physicalFiniteError 5 (criticalFin 4) k ≤ 1/(10:ℝ)^32 := by
  have hb := critical_family_budget_rational
  have hs := ten_step_after_anchor k hk
  have hp := radial_step_positive k
  have hs2 : (radialFourSourceStep k)^2 ≤ (1/(10:ℝ)^22)^2 := by nlinarith [sq_nonneg (radialFourSourceStep k)]
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg (radialFourSourceStep k))
  have hn := mul_le_mul_of_nonneg_left hs2 (show (0:ℝ)≤25*(2:ℝ)^2*(10:ℝ)^10 by positivity)
  unfold physicalFiniteError tenCriticalBudget at *
  norm_num at *
  nlinarith

/-- Explicit integer cutoff for the ORIGINAL critical source. -/
theorem critical_anchor_after_numeric_cutoff (k : ℕ) (hk : 10^22-1 ≤ k) :
    physicalFiniteError 5 (criticalFin 4) k < finiteSourceEnergy 5 (criticalFin 4) k := by
  have hk' : tenAnchorIndex ≤ k := hk
  apply ten_critical_anchor_of_small k hk'
  have h := critical_error_at_numeric_cutoff k hk'
  have hn : (1:ℝ)/(10:ℝ)^32 < 1/(10:ℝ)^30 := by norm_num
  linarith

/-- A numerical lower bound on the completed critical physical energy. -/
theorem critical_energy_lower_after_numeric_cutoff (k : ℕ) (hk : tenAnchorIndex ≤ k) :
    5/(10:ℝ)^30 < finiteSourceEnergy 5 (criticalFin 4) k := by
  have hR := ten_original_inverse_correction_upper
  change sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 4 trialSolve ⬝ᵥ
    ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 4)⁻¹ *ᵥ
      sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 4 trialSolve) < 5/(10:ℝ)^35 at hR
  have hsource := ten_trial_source_lower_after_anchor k hk
  have htrial := ten_trial_tail_budget_after_anchor k hk
  have hcrit := critical_error_at_numeric_cutoff k hk
  have htransfer := finite_critical_transfer 4 k trialSolve ten_old_block_isUnit
    (ten_anchor_cutoff.trans hk)
  rw [trial_fin_source_equal,trial_fin_error_equal] at htransfer
  have ht : (radialFourSourceStep k)^2*familyConstant tenOrders trialCoefficient ≤ 25/(10:ℝ)^34 := by
    simpa only [mul_comm] using htrial
  have hn : (5/(10:ℝ)^30)+(5/(10:ℝ)^35)+(25/(10:ℝ)^34)+(1/(10:ℝ)^32) <
      6/(10:ℝ)^30 := by norm_num
  nlinarith

theorem critical_anchor_at_numeric_cutoff :
    physicalFiniteError 5 (criticalFin 4) (10^22-1) <
      finiteSourceEnergy 5 (criticalFin 4) (10^22-1) :=
  critical_anchor_after_numeric_cutoff _ le_rfl

end
end CarryExplicitBudget
