import PhysicalPickFiveSourceHankel
import Mathlib.Tactic

/-!
The native unshifted 4×4 determinant is strictly positive by the
pre-existing source-derived triangular factorization H₄ = C·Cᵀ.
No all-order positivity or target Pick Gram is assumed.
-/
namespace CarryMaterialPhysicalSevenSource
open CarrySelfAdjointOperator CarryMaterialSourceFactorComparison
open scoped Matrix
noncomputable section
set_option autoImplicit false

theorem canonical_native_unshifted_hankel_four_det_pos :
    0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 4).det := by
  let C := material_hankel_cholesky_four
  have hFactor : C * Cᵀ = hankelGram canonicalCompletedNativeLogDerivativeMoment 4 :=
    material_hankel_cholesky_four_identity
  have hp : 0 < C.det := material_hankel_cholesky_four_det_pos
  rw [← hFactor, Matrix.det_mul, Matrix.det_transpose]
  exact mul_pos hp hp

#print axioms canonical_native_unshifted_hankel_four_det_pos
end
end CarryMaterialPhysicalSevenSource
