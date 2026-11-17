import PhysicalPickEightOddSourceHankel
import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenance
import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrence
import Mathlib.Tactic

/-!
Eight-coordinate odd boundary discriminant is the exact native
Hankel 4×4 determinant, not merely an analogical sign criterion.
The a_j=2h_j bridge establishes its factor 16.
-/
namespace CarrySelfAdjointOperator
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private theorem eight_discriminant_poly_hankel_four
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

theorem nativeSourceEightOddDiscriminant_eq_nativeHankel_four_det :
    nativeSourceEightOddDiscriminant =
      (!![nativeSourceOddBoundaryCoefficient 1, nativeSourceOddBoundaryCoefficient 2,
          nativeSourceOddBoundaryCoefficient 3, nativeSourceOddBoundaryCoefficient 4;
          nativeSourceOddBoundaryCoefficient 2, nativeSourceOddBoundaryCoefficient 3,
          nativeSourceOddBoundaryCoefficient 4, nativeSourceOddBoundaryCoefficient 5;
          nativeSourceOddBoundaryCoefficient 3, nativeSourceOddBoundaryCoefficient 4,
          nativeSourceOddBoundaryCoefficient 5, nativeSourceOddBoundaryCoefficient 6;
          nativeSourceOddBoundaryCoefficient 4, nativeSourceOddBoundaryCoefficient 5,
          nativeSourceOddBoundaryCoefficient 6, nativeSourceOddBoundaryCoefficient 7] :
          Matrix (Fin 4) (Fin 4) ℝ).det := by
  rw [← eight_discriminant_poly_hankel_four]
  unfold nativeSourceEightOddDiscriminant nativeSourceSixOddDiscriminant
    nativeSourceEightOddCoupling0 nativeSourceEightOddCoupling1
    nativeSourceEightOddCoupling2
  ring

theorem nativeSourceEightOddDiscriminant_eq_sixteen_shiftedHankel_four_det :
    nativeSourceEightOddDiscriminant =
      16 * (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 4).det := by
  rw [nativeSourceEightOddDiscriminant_eq_nativeHankel_four_det]
  have hM :
      (!![nativeSourceOddBoundaryCoefficient 1, nativeSourceOddBoundaryCoefficient 2,
          nativeSourceOddBoundaryCoefficient 3, nativeSourceOddBoundaryCoefficient 4;
          nativeSourceOddBoundaryCoefficient 2, nativeSourceOddBoundaryCoefficient 3,
          nativeSourceOddBoundaryCoefficient 4, nativeSourceOddBoundaryCoefficient 5;
          nativeSourceOddBoundaryCoefficient 3, nativeSourceOddBoundaryCoefficient 4,
          nativeSourceOddBoundaryCoefficient 5, nativeSourceOddBoundaryCoefficient 6;
          nativeSourceOddBoundaryCoefficient 4, nativeSourceOddBoundaryCoefficient 5,
          nativeSourceOddBoundaryCoefficient 6, nativeSourceOddBoundaryCoefficient 7] :
            Matrix (Fin 4) (Fin 4) ℝ) =
        (2 : ℝ) • shiftedHankel canonicalCompletedNativeLogDerivativeMoment 4 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shiftedHankel, Matrix.smul_apply,
        nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
        primeDepthGeometricMoment_eq_canonical, smul_eq_mul]
  rw [hM, Matrix.det_smul]
  norm_num

theorem nativeSourceEightOddDiscriminant_pos :
    0 < nativeSourceEightOddDiscriminant := by
  rw [nativeSourceEightOddDiscriminant_eq_sixteen_shiftedHankel_four_det]
  exact mul_pos (by norm_num)
    canonicalCompletedNativeShiftedHankel_four_det_pos

theorem nativeSourceEightOddBoundaryEnergy_strict_pos
    (u v w t : ℂ) (hne : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0 ∨ t ≠ 0) :
    0 < nativeSourceEightOddBoundaryEnergy u v w t :=
  nativeSourceEightOddBoundaryEnergy_pos_iff.mpr
    nativeSourceEightOddDiscriminant_pos u v w t hne

/-- The exact source Schur margin in the new odd coordinate is
TWICE the canonical K4/K3 determinant ratio. This is the original
eight-coordinate coefficient, not a manually chosen quadratic weight. -/
theorem nativeSourceEightOddMargin_eq_two_shiftedHankel_ratio :
    nativeSourceEightOddDiscriminant / nativeSourceSixOddDiscriminant =
      2 * ((shiftedHankel canonicalCompletedNativeLogDerivativeMoment 4).det /
        (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 3).det) := by
  rw [nativeSourceEightOddDiscriminant_eq_sixteen_shiftedHankel_four_det,
      nativeSourceSixOddDiscriminant_eq_eight_shiftedHankel_three_det]
  have hne : (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 3).det ≠ 0 :=
    canonicalCompletedNativeShiftedHankel_three_det_pos.ne'
  field_simp [hne]
  ring

theorem nativeSourceEightOddMargin_pos :
    0 < nativeSourceEightOddDiscriminant / nativeSourceSixOddDiscriminant :=
  div_pos nativeSourceEightOddDiscriminant_pos nativeSourceSixOddDiscriminant_pos

#print axioms nativeSourceEightOddMargin_eq_two_shiftedHankel_ratio
#print axioms nativeSourceEightOddMargin_pos

#print axioms nativeSourceEightOddDiscriminant_eq_sixteen_shiftedHankel_four_det
#print axioms nativeSourceEightOddDiscriminant_pos
#print axioms nativeSourceEightOddBoundaryEnergy_strict_pos

#print axioms nativeSourceEightOddDiscriminant_eq_nativeHankel_four_det

end
end CarrySelfAdjointOperator
