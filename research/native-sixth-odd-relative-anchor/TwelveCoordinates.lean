import TwelveTrial

namespace CarrySixthRelative
open CarrySelfAdjointOperator CarryDirectAnchor CarryIntegralCertificate CarryVariationalSchur
open CarryCriticalSource CarrySummableRadial CarryOddEnergy CarrySixthOdd
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 65536

/-- The upper-left old-prefix portion of the previously checked rational
coordinate matrix, not a modification of the source. -/
def oldCoordinate : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (CarrySixthOdd.trialCoefficient i.val j.val : ℝ)

def oldSource : Matrix (Fin 5) (Fin 5) ℝ :=
  sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 5

def transformedOld : Matrix (Fin 5) (Fin 5) ℝ := oldCoordinateᵀ * oldSource * oldCoordinate

theorem oldCoordinate_upper : oldCoordinate.BlockTriangular id := by
  intro i j hij
  have hh := trial_upper_check ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ (by simpa using hij)
  change (CarrySixthOdd.trialCoefficient i.val j.val : ℝ)=0
  exact_mod_cast hh

theorem oldCoordinate_isUnit : IsUnit oldCoordinate := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_of_upperTriangular oldCoordinate_upper]
  apply isUnit_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  fin_cases i <;> norm_num [oldCoordinate,CarrySixthOdd.trialCoefficient,trialCoefficientData]

theorem oldCoordinate_mulVec_injective : Function.Injective oldCoordinate.mulVec := by
  letI := oldCoordinate_isUnit.invertible
  intro x y h
  have hh := congrArg (fun v => oldCoordinate⁻¹ *ᵥ v) h
  simpa only [Matrix.mulVec_mulVec,Matrix.inv_mul_of_invertible,Matrix.one_mulVec] using hh

theorem transformedOld_posDef : transformedOld.PosDef := by
  have h := CarryThetaPattern.odd_source_five_posDef.conjTranspose_mul_mul_same oldCoordinate_mulVec_injective
  change (oldCoordinate.conjTranspose * oldSource * oldCoordinate).PosDef at h
  have he : oldCoordinate.conjTranspose = oldCoordinateᵀ := by
    ext i j
    simp
  rw [he] at h
  exact h

theorem old_trial_last_row_zero (i : Fin 5) : CarrySixthOdd.trialCoefficient 5 i.val = 0 := by
  have hi := trial_upper_check (5 : Fin 6) ⟨i.val,by omega⟩ (by change i.val < 5; exact i.isLt)
  exact hi

theorem trialPairing_old_truncated (i j : Fin 5) :
    trialPairing i.val j.val = ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5,
      (CarrySixthOdd.trialCoefficient a i.val:ℝ)*h (a+b+1)*
        (CarrySixthOdd.trialCoefficient b j.val:ℝ) := by
  unfold trialPairing
  rw [Finset.sum_range_succ]
  simp only [old_trial_last_row_zero i,Rat.cast_zero,zero_mul,Finset.sum_const_zero,add_zero]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_range_succ]
  simp only [old_trial_last_row_zero j,Rat.cast_zero,mul_zero,add_zero]

/-- The actual old source after congruence, including every crossing. -/
theorem transformedOld_entry (i j : Fin 5) : transformedOld i j = trialPairing i.val j.val := by
  rw [trialPairing_old_truncated]
  simp only [transformedOld,Matrix.mul_apply,Matrix.transpose_apply,oldCoordinate,oldSource,
    sourceMomentMatrix,Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin 5,
    (CarrySixthOdd.trialCoefficient a i.val:ℝ)*canonicalCompletedNativeLogDerivativeMoment (a+b.val+1)*
      (CarrySixthOdd.trialCoefficient b.val j.val:ℝ)) 5]
  apply Finset.sum_congr rfl
  intro a _
  exact Fin.sum_univ_eq_sum_range (fun b =>
    (CarrySixthOdd.trialCoefficient a i.val:ℝ)*canonicalCompletedNativeLogDerivativeMoment (a+b+1)*
      (CarrySixthOdd.trialCoefficient b j.val:ℝ)) 5

end
end CarrySixthRelative
