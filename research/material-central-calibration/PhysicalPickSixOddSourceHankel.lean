import CarrySelfAdjointOperator.CompletedNativeChiralReturnTwelfthSourceIntegral
import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenance
import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrence
import CarrySelfAdjointOperator.LogarithmicMomentHankel
import Mathlib.Tactic

/-!
C2's physical order-twelve odd source discriminant determines the
canonical shifted 3×3 Hankel margin exactly. The normalization is
a_j = 2 h_j from the *independent* prime-depth readout, not a
new positivity or Gram assumption.
-/
namespace CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false

theorem nativeSourceSixOddDiscriminant_eq_eight_shiftedHankel_three_det :
    nativeSourceSixOddDiscriminant =
      8 * (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 3).det := by
  unfold nativeSourceSixOddDiscriminant
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical]
  rw [Matrix.det_fin_three]
  norm_num [shiftedHankel]
  ring

theorem canonicalCompletedNativeShiftedHankel_three_det_pos :
    0 < (shiftedHankel canonicalCompletedNativeLogDerivativeMoment 3).det := by
  have h := nativeSourceSixOddDiscriminant_pos
  rw [nativeSourceSixOddDiscriminant_eq_eight_shiftedHankel_three_det] at h
  nlinarith

#print axioms nativeSourceSixOddDiscriminant_eq_eight_shiftedHankel_three_det
#print axioms canonicalCompletedNativeShiftedHankel_three_det_pos

end
end CarrySelfAdjointOperator
