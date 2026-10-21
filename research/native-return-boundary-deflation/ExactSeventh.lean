import ResidualTest
import SixthEvenCertificate

/-! A regression on the EXACT PR41 monic degree-six residual. The only finite
positivity consumed here concerns its OLD six-dimensional prefix. No seventh
pivot sign or rational replacement for the residual is an input. -/
namespace CarryReturnDeflation
open CarrySelfAdjointOperator NativeMomentOrthogonalization GeometryOfNumbers.Analysis
open Filter Topology
noncomputable section
set_option autoImplicit false

theorem exact_seventh_head_cross_zero :
    canonicalBoundaryPair 7 (headBoundary 6) (nativeResidualBoundary 0 6) = 0 := by
  apply pr41_even_head_cross_zero 6 (by norm_num)
  intro r hr
  exact ne_of_gt (CarrySixthEven.even_six_pivots_pos r hr)

theorem exact_seventh_projected_tendsto_zero :
    Tendsto (fun k => projectedJetPair 7 k (nativeResidualBoundary 0 6)
      (nativeResidualBoundary 0 6)) atTop (nhds 0) :=
  head_orthogonal_projected_tendsto_zero 6 _ _ exact_seventh_head_cross_zero

theorem exact_seventh_remaining_energy_tendsto :
    Tendsto (fun k => (jetSchurRemainder 7 k (nativeResidualBoundary 0 6)
      (nativeResidualBoundary 0 6)).re) atTop
      (nhds (2*carryPairingPivot (hankelPairing canonicalCompletedNativeLogDerivativeMoment) 6)) := by
  simpa only [Fin.val_zero,Nat.add_zero] using
    residual_energy_tendsto_of_projected_zero 0 6 exact_seventh_projected_tendsto_zero

end
end CarryReturnDeflation
