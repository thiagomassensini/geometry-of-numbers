import CanonicalBalance

/-! A synthetic algebraic control, never substituted for the canonical source.
It tests whether the stated prefix and recurrence data suffice for a sign law. -/
namespace CarryCriticalEulerControl
open CarrySelfAdjointOperator CarryCriticalEuler Matrix
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def controlMoment : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | _ => 1

def controlCoefficient : ℕ → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => 0
  | 3 => -1/3
  | 4 => 1/3
  | _ => 0

theorem control_moment_positive (k : ℕ) : 0 < controlMoment k := by
  unfold controlMoment
  split <;> norm_num

theorem control_recurrence_prefix (n : ℕ) (hn : n<4) :
    ((n+1:ℕ):ℝ)*controlCoefficient (n+1) +
      ∑ k ∈ Finset.range (n+1), controlMoment k * controlCoefficient (n-k) = 0 := by
  interval_cases n <;> norm_num [controlCoefficient,controlMoment,Finset.sum_range_succ]

theorem control_old_matrix : sourceMomentMatrix controlMoment 0 1 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [sourceMomentMatrix,controlMoment]

theorem control_old_positive : (sourceMomentMatrix controlMoment 0 1).PosDef := by
  rw [control_old_matrix]
  exact Matrix.PosDef.one

theorem control_shifted_old_positive : (sourceMomentMatrix controlMoment 1 1).PosDef := by
  have h : sourceMomentMatrix controlMoment 1 1 = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [sourceMomentMatrix,controlMoment]
  rw [h]
  exact Matrix.PosDef.one

def controlVector : Fin 2 → ℝ :=
  MomentosHankel.schurVector (sourceMomentMatrix controlMoment 0 1)
    (sourceMomentCoupling controlMoment 0 1)

theorem control_vector_exact : controlVector = ![-1,1] := by
  unfold controlVector MomentosHankel.schurVector
  rw [control_old_matrix]
  ext i
  fin_cases i
  · norm_num [sourceMomentCoupling,controlMoment]
  · change Fin.snoc _ 1 (Fin.last 1) = 1
    rw [Fin.snoc_last]

theorem control_pivot_positive : sourceMomentSchur controlMoment 0 1 = 1 := by
  rw [sourceMomentSchur,control_old_matrix]
  norm_num [sourceMomentCoupling,controlMoment,dotProduct]

theorem control_weighted_negative : weightedForm controlMoment 0 controlVector = -16 := by
  rw [control_vector_exact]
  norm_num [weightedForm,Fin.sum_univ_two,controlMoment]

theorem control_shifted_balance_negative : sourceMomentQuadratic controlMoment 1 2 controlVector = -2 := by
  rw [control_vector_exact]
  norm_num [sourceMomentQuadratic,Matrix.mulVec,dotProduct,sourceMomentMatrix,controlMoment,Fin.sum_univ_two]

/-- Even the enlarged unshifted block is positive; the missing shifted
source balance is the part that defeats the proposed generic sign inference. -/
theorem control_enlarged_positive : (sourceMomentMatrix controlMoment 0 2).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (sourceMomentMatrix_isHermitian _ _ _)
  intro x hx
  have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    ext i
    fin_cases i <;> simp [h]
  have he : star x ⬝ᵥ (sourceMomentMatrix controlMoment 0 2 *ᵥ x) =
      (x 0+x 1)^2+(x 1)^2 := by
    simp [sourceMomentMatrix,controlMoment,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring
  rw [he]
  rcases hne with h0|h1
  · by_cases h1 : x 1 = 0
    · simpa [h1] using sq_pos_of_ne_zero h0
    · nlinarith [sq_nonneg (x 0+x 1),sq_pos_of_ne_zero h1]
  · nlinarith [sq_nonneg (x 0+x 1),sq_pos_of_ne_zero h1]

end
end CarryCriticalEulerControl
