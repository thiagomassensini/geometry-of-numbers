import TwelveResidual
import TwelveCoercive

namespace CarrySixthRelative
open CarrySelfAdjointOperator CarryDirectAnchor CarryIntegralCertificate CarryVariationalSchur
open CarryCriticalSource CarrySummableRadial CarryOddEnergy CarrySixthOdd
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000

/-- All five transformed old-new crossings of the original residual. -/
def transformedResidual : Fin 5 → ℝ :=
  oldCoordinateᵀ *ᵥ sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve

theorem transformed_residual_bounded (i : Fin 5) :
    |transformedResidual i| ≤ 1/(50*(10:ℝ)^18) := by
  unfold transformedResidual
  rw [transformed_residual_entry,abs_div,abs_of_pos (show (0:ℝ)<(10:ℝ)^18 by positivity)]
  have h := div_le_div_of_nonneg_right (trial_cross_bounded i) (show (0:ℝ)≤(10:ℝ)^18 by positivity)
  calc
    |trialPairing i.val 5|/(10:ℝ)^18 ≤ (1/50:ℝ)/(10:ℝ)^18 := h
    _ = 1/(50*(10:ℝ)^18) := by norm_num

theorem transformed_residual_square_bound :
    transformedResidual ⬝ᵥ transformedResidual ≤ 2/(10:ℝ)^39 := by
  have hs (i : Fin 5) : (transformedResidual i)^2 ≤ (1/(50*(10:ℝ)^18))^2 := by
    have h := transformed_residual_bounded i
    have hnon := abs_nonneg (transformedResidual i)
    have hm := mul_self_le_mul_self hnon h
    simpa [sq_abs,pow_two] using hm
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  have h4 := hs 4
  simp only [dotProduct,Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num at *
  simp only [show (Fin.succ (2:Fin 4))=(3:Fin 5) from rfl,
    show (Fin.succ (Fin.succ (2:Fin 3)))=(4:Fin 5) from rfl] at *
  nlinarith

theorem original_inverse_correction_upper :
    sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve ⬝ᵥ
      ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 5)⁻¹ *ᵥ
        sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve) ≤ 1/(10:ℝ)^38 := by
  have h := inverseResidual_bound transformedOld transformedOld_posDef (1/5) (by norm_num)
    transformed_old_coercive transformedResidual
  have hs := transformed_residual_square_bound
  have he := congruence_inverse_residual oldCoordinate oldSource
    (sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve)
    oldCoordinate_isUnit twelve_old_isUnit
  change _ = transformedResidual ⬝ᵥ (transformedOld⁻¹ *ᵥ transformedResidual) at he
  dsimp only [oldSource] at he
  rw [he]
  norm_num at *
  nlinarith

end
end CarrySixthRelative
