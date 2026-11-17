import PhysicalPickSevenNative
import KnownMargins
import CarrySelfAdjointOperator.CompletedNativeChiralReturnEightBoundaryFace
import Mathlib.Tactic

/-! The canonical odd Hankel K4 is already strictly positive in the
unmodified material-source eight-face certificate of GoN.
No new Gram, weights, characteristic, or positivity premise. -/
namespace CarrySelfAdjointOperator
open CarryCriticalSource CarryMaterialSourceFactorComparison
open scoped Matrix
noncomputable section
set_option autoImplicit false

theorem canonicalCompletedNativeShiftedHankel_four_posDef :
    (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 4).PosDef := by
  have hsource := sourceMatrices_through_four_posDef (1 : Fin 2) 4 (by omega)
  convert hsource using 1
  ext i j
  rfl

theorem canonicalCompletedNativeShiftedHankel_four_det_pos :
    0 < (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 4).det :=
  canonicalCompletedNativeShiftedHankel_four_posDef.det_pos

#print axioms canonicalCompletedNativeShiftedHankel_four_det_pos
end
end CarrySelfAdjointOperator
