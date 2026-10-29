import EightMargin
import EightSchurCore

namespace CarryCriticalRadialMargin
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction
open CarryMaterialVariation CarrySummableRadial CarryIntegralCertificate NativeLaguerre
open NativeMomentOrthogonalization Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 65536

theorem eight_boundary_positive_via_general_tail : 0 < oddCanonicalForm eightOrders eightCoefficients := by
  apply finite_odd_boundary_positive_of_anchor eightOrders eightCoefficients budgetIndex
  · have hcut : oddGridCutoff eightOrders = 32 := by decide +kernel
    rw [hcut]
    norm_num [budgetIndex]
  · exact eight_anchor_beats_general_tail

theorem fourth_odd_schur_positive_via_source_anchor :
    0 < sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 1 3 := by
  rw [← eight_form_eq_original_schur]
  exact eight_boundary_positive_via_general_tail

end
end CarryCriticalRadialMargin
