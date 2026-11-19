import CanonicalComparison
import Mathlib.Tactic

/-!
Unshifted third moment Hankel determinant: obtain strict sign
from the already-certified material triangular factor of the
canonical 4×4 Hankel. The factor was NOT defined from the
target Pick matrix or any 5-point positivity assumption.
-/
namespace CarryMaterialPhysicalFiveSource
open CarrySelfAdjointOperator CarryMaterialSourceFactorComparison
open scoped Matrix

theorem canonical_native_unshifted_hankel_three_posDef :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 3).PosDef := by
  let C := material_hankel_cholesky_four
  let H := hankelGram canonicalCompletedNativeLogDerivativeMoment 4
  have hFactor : C * Cᵀ = H := by
    exact material_hankel_cholesky_four_identity
  have hPSD : H.PosSemidef := by
    rw [← hFactor]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose C
  have hC : 0 < C.det := material_hankel_cholesky_four_det_pos
  have hNonzero : H.det ≠ 0 := by
    rw [← hFactor, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hC.ne' hC.ne'
  have hPD : H.PosDef := hPSD.posDef_iff_det_ne_zero.mpr hNonzero
  have hSub := hPD.submatrix (e := Fin.castSucc) (Fin.castSucc_injective 3)
  convert hSub using 1
  ext i j
  rfl

theorem canonical_native_unshifted_hankel_three_det_pos :
    0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 3).det :=
  canonical_native_unshifted_hankel_three_posDef.det_pos

#print axioms canonical_native_unshifted_hankel_three_det_pos
end CarryMaterialPhysicalFiveSource
