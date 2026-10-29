import EntrywiseSquare
import OddSourceBoxes

namespace CarryEntrywiseSquare
open CarrySixthOdd CarryIntegralCertificate CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536

/-- Reuse exact theta-source bounds already compiled for the ORIGINAL h.
No rounded checkpoint and no spectrum is an input to this theorem. -/
theorem native_first_pair :
    0 < canonicalCompletedNativeLogDerivativeMoment 0 ∧
    0 < canonicalCompletedNativeLogDerivativeMoment 1 ∧
    canonicalCompletedNativeLogDerivativeMoment 1 <
      canonicalCompletedNativeLogDerivativeMoment 0 ∧
    canonicalCompletedNativeLogDerivativeMoment 0 < 1 := by
  have hzero := mem_compactMomentBox 0
  have hone := mem_compactMomentBox 1
  norm_num [compactMomentBox, compactMomentTable, Box.Mem, intervalScale] at hzero hone
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The literal proposal fails already in dimension one for native moments.
The squared-moment Jacobi eigenvalue is below 1; the original height is above 1. -/
theorem native_squared_eigenvalue_not_height :
    singletonEigenvalue (squaredMoments canonicalCompletedNativeLogDerivativeMoment) < 1 ∧
      1 < (Real.sqrt (singletonEigenvalue canonicalCompletedNativeLogDerivativeMoment))⁻¹ :=
  singleton_square_not_height _ native_first_pair.1 native_first_pair.2.1
    native_first_pair.2.2.1

theorem native_squared_mass_changed :
    squaredMoments canonicalCompletedNativeLogDerivativeMoment 0 <
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  change canonicalCompletedNativeLogDerivativeMoment 0 ^ 2 < _
  have := native_first_pair
  nlinarith [this.1, this.2.2.2]

end
end CarryEntrywiseSquare
