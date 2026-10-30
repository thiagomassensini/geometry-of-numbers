import TwelveCorrection

namespace CarrySixthExplicit
open CarrySelfAdjointOperator CarrySixthRelative CarryDirectAnchor CarryVariationalSchur
open CarryCriticalSource CarrySixthOdd CarrySummableRadial
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536

/-- The complete old-block solve, transported by the rational congruence. -/
theorem congruence_inverse_apply {n : ℕ} (P A : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (hP : IsUnit P) (hA : IsUnit A) :
    A⁻¹ *ᵥ r = P *ᵥ ((Pᵀ * A * P)⁻¹ *ᵥ (Pᵀ *ᵥ r)) := by
  let w := A⁻¹ *ᵥ r
  let u := P⁻¹ *ᵥ w
  letI := hA.invertible
  letI := hP.invertible
  have hw : A *ᵥ w = r := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hpu : P *ᵥ u = w := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hbu : (Pᵀ * A * P) *ᵥ u = Pᵀ *ᵥ r := by
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hpu,hw]
  have hB : IsUnit (Pᵀ * A * P) := (((Matrix.isUnit_transpose P).mpr hP).mul hA).mul hP
  letI := hB.invertible
  have he := congrArg (fun v => (Pᵀ * A * P)⁻¹ *ᵥ v) hbu
  rw [Matrix.mulVec_mulVec,Matrix.inv_mul_of_invertible,Matrix.one_mulVec] at he
  change w = _
  rw [← he,hpu]

def transformedSolve : Fin 5 → ℝ := transformedOld⁻¹ *ᵥ transformedResidual

theorem transformed_solve_norm_bound : transformedSolve ⬝ᵥ transformedSolve ≤ 5/(10:ℝ)^38 := by
  have hu : transformedOld *ᵥ transformedSolve = transformedResidual := by
    letI := transformedOld_posDef.isUnit.invertible
    unfold transformedSolve
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hc := transformed_old_coercive transformedSolve
  rw [hu,dotProduct_comm transformedSolve transformedResidual] at hc
  have hr := inverseResidual_bound transformedOld transformedOld_posDef (1/5) (by norm_num)
    transformed_old_coercive transformedResidual
  change (1/5:ℝ)*(transformedResidual ⬝ᵥ transformedSolve) ≤
    transformedResidual ⬝ᵥ transformedResidual at hr
  have hs := transformed_residual_square_bound
  norm_num at *
  nlinarith

theorem transformed_solve_component_bound (i : Fin 5) :
    |transformedSolve i| ≤ 3/(10:ℝ)^19 := by
  have hs : (transformedSolve i)^2 ≤ transformedSolve ⬝ᵥ transformedSolve := by
    unfold dotProduct
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (transformedSolve j))
      (Finset.mem_univ i)
    simpa [pow_two] using h
  have hn := transformed_solve_norm_bound
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (transformedSolve i - 3/(10:ℝ)^19),
    sq_nonneg (transformedSolve i + 3/(10:ℝ)^19)]

theorem old_coordinate_entry_bound (i j : Fin 5) : |oldCoordinate i j| ≤ (10:ℝ)^16 := by
  fin_cases i <;> fin_cases j <;> norm_num [oldCoordinate,CarrySixthOdd.trialCoefficient,trialCoefficientData]

theorem original_solve_correction_bound (i : Fin 5) :
    |(oldSource⁻¹ *ᵥ sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve) i| ≤ 1 := by
  rw [congruence_inverse_apply oldCoordinate oldSource _ oldCoordinate_isUnit twelve_old_isUnit]
  change |(oldCoordinate *ᵥ transformedSolve) i| ≤ 1
  unfold Matrix.mulVec dotProduct
  calc
    _ ≤ ∑ j : Fin 5, |oldCoordinate i j*transformedSolve j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 5, (10:ℝ)^16*(3/(10:ℝ)^19) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (old_coordinate_entry_bound i j) (transformed_solve_component_bound j)
        (abs_nonneg _) (by positivity)
    _ ≤ 1 := by norm_num

theorem twelve_trial_coefficient_bound (i : ℕ) (hi : i ∈ twelveOrders) :
    |twelveCoeff i| ≤ 1 := by
  have hi' : i < 6 := Finset.mem_range.mp hi
  interval_cases i <;> norm_num [twelveCoeff,CarrySixthOdd.trialCoefficient,trialCoefficientData]

theorem critical_old_coefficient_identity (i : Fin 5) :
    criticalFin 5 i.castSucc = twelveCoeff i.val -
      (oldSource⁻¹ *ᵥ sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve) i := by
  have h := sourceTrialResidual_inverse_of_isUnit canonicalCompletedNativeLogDerivativeMoment
    1 5 twelve_old_isUnit twelveSolve
  have hi := congrFun h i
  change (oldSource⁻¹ *ᵥ sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve) i =
    (oldSource⁻¹ *ᵥ sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment 1 5) i - twelveSolve i at hi
  simp only [criticalFin,Fin.snoc_castSucc,Pi.neg_apply,oldSource]
  simp only [twelveSolve,oldSource] at hi
  linarith

theorem critical_coefficient_bound (i : Fin 6) : |criticalFin 5 i| ≤ 2 := by
  by_cases hi : i.val < 5
  · let j : Fin 5 := ⟨i.val,hi⟩
    have hindex : j.castSucc=i := by ext; rfl
    rw [← hindex,critical_old_coefficient_identity]
    have ht := twelve_trial_coefficient_bound j.val (by apply Finset.mem_range.mpr; have hj := j.isLt; omega)
    have hr := original_solve_correction_bound j
    have habs := abs_sub (twelveCoeff j.val)
      ((oldSource⁻¹ *ᵥ sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 5 twelveSolve) j)
    linarith
  · have he : i=5 := by ext; omega
    subst i
    norm_num [criticalFin,Fin.snoc]

end
end CarrySixthExplicit
