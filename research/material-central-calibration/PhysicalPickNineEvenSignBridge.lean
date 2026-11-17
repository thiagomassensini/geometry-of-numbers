import PhysicalPickNineEvenSourceHankel
import PhysicalPickEightDiscriminantBridge
import CarrySelfAdjointOperator.CompletedNativeChiralReturnFourteenthSourceIntegral
import Mathlib.Tactic

/-!
The ninth C2 direction is EVEN, rather than the eighth ODD one.
Original boundary coefficients a_j = 2*h_j determine the raw even
source matrix without a new norm or manufactured positive Gram.
The actual C2 source fifth-even Schur pivot has all couplings retained.
-/
namespace CarrySelfAdjointOperator
open CarryCriticalSource CarryMaterialPhysicalSevenSource
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

/-- Original even-sector boundary coefficients; only their finite indexing
is named here. The green source and its normalization are unchanged. -/
def nativeSourceNineEvenRawMatrix : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => nativeSourceOddBoundaryCoefficient (i.val+j.val)

def nativeSourceNineEvenRawDiscriminant : ℝ :=
  nativeSourceNineEvenRawMatrix.det

theorem nativeSourceNineEvenRawMatrix_eq_two_hankel_five :
    nativeSourceNineEvenRawMatrix =
      (2 : ℝ) • hankelGram canonicalCompletedNativeLogDerivativeMoment 5 := by
  ext i j
  simp [nativeSourceNineEvenRawMatrix, hankelGram, Matrix.smul_apply,
    nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical, smul_eq_mul]

theorem nativeSourceNineEvenRawDiscriminant_eq_thirtytwo_hankel_five_det :
    nativeSourceNineEvenRawDiscriminant =
      32 * (hankelGram canonicalCompletedNativeLogDerivativeMoment 5).det := by
  rw [nativeSourceNineEvenRawDiscriminant,
    nativeSourceNineEvenRawMatrix_eq_two_hankel_five, Matrix.det_smul]
  norm_num

private theorem even_four_discriminant_poly_hankel_four
    (a b c d e f g : ℝ) :
    (a*c*e + 2*b*c*d - a*d^2 - b^2*e - c^3)*g +
      d*(b*e^2 - 2*c*d*e + d^3 - b*d*f + c^2*f) -
      e*(a*e^2 - b*d*e + c*d^2 - c^2*e - a*d*f + b*c*f) +
      f*(a*d*e - b*c*e - b*d^2 + c^2*d - a*c*f + b^2*f) =
      (!![a,b,c,d;b,c,d,e;c,d,e,f;d,e,f,g] : Matrix (Fin 4) (Fin 4) ℝ).det := by
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.sum_univ_succ, Finset.sum_singleton, Fin.succAbove]
  ring

theorem nativeSourceSevenEvenDiscriminant_eq_nativeHankel_four_det :
    nativeSourceSevenEvenDiscriminant =
      (!![nativeSourceOddBoundaryCoefficient 0, nativeSourceOddBoundaryCoefficient 1,
          nativeSourceOddBoundaryCoefficient 2, nativeSourceOddBoundaryCoefficient 3;
          nativeSourceOddBoundaryCoefficient 1, nativeSourceOddBoundaryCoefficient 2,
          nativeSourceOddBoundaryCoefficient 3, nativeSourceOddBoundaryCoefficient 4;
          nativeSourceOddBoundaryCoefficient 2, nativeSourceOddBoundaryCoefficient 3,
          nativeSourceOddBoundaryCoefficient 4, nativeSourceOddBoundaryCoefficient 5;
          nativeSourceOddBoundaryCoefficient 3, nativeSourceOddBoundaryCoefficient 4,
          nativeSourceOddBoundaryCoefficient 5, nativeSourceOddBoundaryCoefficient 6] :
          Matrix (Fin 4) (Fin 4) ℝ).det := by
  rw [← even_four_discriminant_poly_hankel_four]
  unfold nativeSourceSevenEvenDiscriminant nativeSourceFiveEvenDiscriminant
    nativeSourceSevenEvenCoupling0 nativeSourceSevenEvenCoupling1
    nativeSourceSevenEvenCoupling2
  ring

theorem nativeSourceSevenEvenDiscriminant_eq_sixteen_hankel_four_det :
    nativeSourceSevenEvenDiscriminant =
      16 * (hankelGram canonicalCompletedNativeLogDerivativeMoment 4).det := by
  rw [nativeSourceSevenEvenDiscriminant_eq_nativeHankel_four_det]
  have hM :
      (!![nativeSourceOddBoundaryCoefficient 0, nativeSourceOddBoundaryCoefficient 1,
          nativeSourceOddBoundaryCoefficient 2, nativeSourceOddBoundaryCoefficient 3;
          nativeSourceOddBoundaryCoefficient 1, nativeSourceOddBoundaryCoefficient 2,
          nativeSourceOddBoundaryCoefficient 3, nativeSourceOddBoundaryCoefficient 4;
          nativeSourceOddBoundaryCoefficient 2, nativeSourceOddBoundaryCoefficient 3,
          nativeSourceOddBoundaryCoefficient 4, nativeSourceOddBoundaryCoefficient 5;
          nativeSourceOddBoundaryCoefficient 3, nativeSourceOddBoundaryCoefficient 4,
          nativeSourceOddBoundaryCoefficient 5, nativeSourceOddBoundaryCoefficient 6] :
          Matrix (Fin 4) (Fin 4) ℝ) =
        (2 : ℝ) • hankelGram canonicalCompletedNativeLogDerivativeMoment 4 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hankelGram, Matrix.smul_apply,
        nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
        primeDepthGeometricMoment_eq_canonical, smul_eq_mul]
  rw [hM, Matrix.det_smul]
  norm_num

/-- The exact NEW raw source determinant ratio (four old even directions,
fifth even coordinate), retaining all off-diagonal old-new couplings. -/
theorem nativeSourceNineEvenRawRatio_eq_two_hankel_ratio :
    nativeSourceNineEvenRawDiscriminant / nativeSourceSevenEvenDiscriminant =
      2 * ((hankelGram canonicalCompletedNativeLogDerivativeMoment 5).det /
        (hankelGram canonicalCompletedNativeLogDerivativeMoment 4).det) := by
  rw [nativeSourceNineEvenRawDiscriminant_eq_thirtytwo_hankel_five_det,
      nativeSourceSevenEvenDiscriminant_eq_sixteen_hankel_four_det]
  have hne : (hankelGram canonicalCompletedNativeLogDerivativeMoment 4).det ≠ 0 :=
    canonical_native_unshifted_hankel_four_det_pos.ne'
  field_simp [hne]
  ring

theorem nativeSourceNineEvenRawDiscriminant_pos :
    0 < nativeSourceNineEvenRawDiscriminant := by
  rw [nativeSourceNineEvenRawDiscriminant_eq_thirtytwo_hankel_five_det]
  exact mul_pos (by norm_num) canonicalCompletedNativeUnshiftedHankel_five_det_pos

theorem nativeSourceNineEvenRawRatio_pos :
    0 < nativeSourceNineEvenRawDiscriminant / nativeSourceSevenEvenDiscriminant :=
  div_pos nativeSourceNineEvenRawDiscriminant_pos nativeSourceSevenEvenDiscriminant_pos

/-- The previously-proved C2 source recurrence and *original* inverse
coupling give the actual new real even Schur pivot, not a diagonal bound. -/
theorem nativeSourceNineEvenOriginalPivot_pos :
    0 < sourceMomentSchur h 0 4 := fifth_even_pivot_pos

/-- Exact residual of the ORIGINAL source matrix, retaining its inverse
coupling and the scaling a_j = 2*h_j. No raw 5x5 positivity is assumed. -/
theorem nativeSourceNineEvenOriginalQuadratic_sewing
    (x : Fin 4 → ℝ) (t : ℝ) :
    2 * sourceMomentQuadratic h 0 5 (Fin.snoc x t) =
      2 * sourceMomentQuadratic h 0 4
        (x + t • ((sourceMomentMatrix h 0 4)⁻¹ *ᵥ sourceMomentCoupling h 0 4)) +
      (2 * sourceMomentSchur h 0 4)*t^2 := by
  rw [sourceMomentSchur_sewing h 0 4
    (sourceMatrices_through_four_posDef (0 : Fin 2) 4 (by omega))]
  ring

theorem nativeSourceNineEvenCriticalDirection_energy :
    2 * sourceMomentQuadratic h 0 5
      (Fin.snoc
        (-((sourceMomentMatrix h 0 4)⁻¹ *ᵥ sourceMomentCoupling h 0 4))
        (1 : ℝ)) =
      2 * sourceMomentSchur h 0 4 := by
  rw [sourceMomentSchur_critical_direction h 0 4
    (sourceMatrices_through_four_posDef (0 : Fin 2) 4 (by omega))]

#print axioms nativeSourceNineEvenRawDiscriminant_eq_thirtytwo_hankel_five_det
#print axioms nativeSourceSevenEvenDiscriminant_eq_sixteen_hankel_four_det
#print axioms nativeSourceNineEvenOriginalPivot_pos
#print axioms nativeSourceNineEvenRawRatio_eq_two_hankel_ratio
#print axioms nativeSourceNineEvenRawDiscriminant_pos
#print axioms nativeSourceNineEvenOriginalQuadratic_sewing
#print axioms nativeSourceNineEvenCriticalDirection_energy

end
end CarrySelfAdjointOperator
