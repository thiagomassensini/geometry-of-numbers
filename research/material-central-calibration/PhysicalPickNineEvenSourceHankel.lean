import PhysicalPickEightNative
import KnownMargins
import Mathlib.Tactic

/-! Nine-point even source sign comes from the PREEXISTING native
C2 material factorization H5 = restoredEvenFiveFactor *
(restoredEvenFiveFactor)ᵀ, with its full coupling to earlier depths.
No kernel/metric/weights are chosen to fit a desired sign. -/
namespace CarrySelfAdjointOperator
open CarryCriticalSource CarryMaterialSourceFactorComparison
open scoped Matrix
noncomputable section
set_option autoImplicit false

theorem canonicalCompletedNativeUnshiftedHankel_five_posDef :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 5).PosDef := by
  have hsource := even_source_five_posDef
  convert hsource using 1
  ext i j
  rfl

theorem canonicalCompletedNativeUnshiftedHankel_five_det_pos :
    0 < (hankelGram canonicalCompletedNativeLogDerivativeMoment 5).det :=
  canonicalCompletedNativeUnshiftedHankel_five_posDef.det_pos

theorem canonicalCompletedNativeUnshiftedHankel_five_factor :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 5) =
       restoredEvenFiveFactor * restoredEvenFiveFactorᵀ := by
  have he :
      hankelGram canonicalCompletedNativeLogDerivativeMoment 5 =
        sourceMomentMatrix h 0 5 := by
    ext i j
    rfl
  exact he.trans restoredEvenFiveFactor_identity.symm

theorem canonicalCompletedNativeUnshiftedHankel_five_det_eq_factor_sq :
    (hankelGram canonicalCompletedNativeLogDerivativeMoment 5).det =
      restoredEvenFiveFactor.det * restoredEvenFiveFactor.det := by
  rw [canonicalCompletedNativeUnshiftedHankel_five_factor,
      Matrix.det_mul, Matrix.det_transpose]

#print axioms canonicalCompletedNativeUnshiftedHankel_five_posDef
#print axioms canonicalCompletedNativeUnshiftedHankel_five_det_pos
#print axioms canonicalCompletedNativeUnshiftedHankel_five_det_eq_factor_sq

end
end CarrySelfAdjointOperator
