import PhysicalPickNineEvenSignBridge
import Mathlib.Tactic

/-!
Link the ORIGINAL old-new source Schur residual to the exact
determinant quotient. Uses the generic block determinant theorem,
not a 5×5 polynomial expansion.
-/
namespace CarrySelfAdjointOperator
open CarryCriticalSource CarryMaterialPhysicalSevenSource
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

private def evenNineSchurSplit : (Fin 4 ⊕ Fin 1) ≃ Fin 5 :=
  Equiv.ofBijective (fun s => match s with
    | Sum.inl i => Fin.castSucc i
    | Sum.inr _ => Fin.last 4) (by decide)

theorem nativeEvenFiveDet_eq_four_det_mul_sourceSchur :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 5).det =
      (hankelGram canonicalCompletedNativeLogDerivativeMoment 4).det *
        sourceMomentSchur h 0 4 := by
  let A : Matrix (Fin 4) (Fin 4) ℝ := sourceMomentMatrix h 0 4
  let B : Matrix (Fin 4) (Fin 1) ℝ := fun i _ => h (i.val+4)
  let C : Matrix (Fin 1) (Fin 4) ℝ := fun _ j => h (j.val+4)
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => h 8
  have hA : A.PosDef := sourceMatrices_through_four_posDef (0 : Fin 2) 4 (by omega)
  letI : Invertible A :=
    Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hblock :
      (sourceMomentMatrix h 0 5).submatrix evenNineSchurSplit evenNineSchurSplit =
      Matrix.fromBlocks A B C D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [evenNineSchurSplit,sourceMomentMatrix,A,B,C,D,Matrix.fromBlocks]
  have hschur :
      (D - C * ⅟A * B).det = sourceMomentSchur h 0 4 := by
    rw [Matrix.det_unique]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.sum_univ_zero]
    simp only [sourceMomentSchur, sourceMomentCoupling, dotProduct, Matrix.mulVec,
      A, B, C, D, Matrix.invOf_eq_nonsing_inv, Fin.sum_univ_succ, Fin.sum_univ_zero]
    ring
  have hH : (hankelGram canonicalCompletedNativeLogDerivativeMoment 5).det =
      (sourceMomentMatrix h 0 5).det := by
    congr 1
  have hAeq : (hankelGram canonicalCompletedNativeLogDerivativeMoment 4).det =
      A.det := by
    congr 1
  calc
    _ = (sourceMomentMatrix h 0 5).det := hH
    _ = ((sourceMomentMatrix h 0 5).submatrix
        evenNineSchurSplit evenNineSchurSplit).det :=
        (Matrix.det_submatrix_equiv_self evenNineSchurSplit (sourceMomentMatrix h 0 5)).symm
    _ = (Matrix.fromBlocks A B C D).det := by rw [hblock]
    _ = A.det * (D - C * ⅟A * B).det := Matrix.det_fromBlocks₁₁ A B C D
    _ = _ := by rw [hAeq, hschur]

theorem nativeSourceNineEvenRawRatio_eq_twice_originalPivot :
    nativeSourceNineEvenRawDiscriminant / nativeSourceSevenEvenDiscriminant =
      2 * sourceMomentSchur h 0 4 := by
  rw [nativeSourceNineEvenRawRatio_eq_two_hankel_ratio,
    nativeEvenFiveDet_eq_four_det_mul_sourceSchur]
  have hne : (hankelGram canonicalCompletedNativeLogDerivativeMoment 4).det ≠ 0 :=
    canonical_native_unshifted_hankel_four_det_pos.ne'
  field_simp [hne]

#print axioms nativeEvenFiveDet_eq_four_det_mul_sourceSchur
#print axioms nativeSourceNineEvenRawRatio_eq_twice_originalPivot

end
end CarrySelfAdjointOperator
