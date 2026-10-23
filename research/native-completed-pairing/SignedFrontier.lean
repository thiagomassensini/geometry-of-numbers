import CompletionControls
import CarrySelfAdjointOperator.CompletedC3FullWronskianPolarization

namespace CarryCompletedPairing
open CarryCameraTail CarryMaterialTheta CarryFourLeg CarryGreenProvenance
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- The existing full completed operator is reused with its existing
metric. This is a symplectic readout, not an adjoint square. -/
theorem integral_pairing_full_operator (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    completedIntegralPairing M M z w =
      canonicalCompletedC3NormalizedFullWronskianOperatorKernel M w z := by
  rw [completed_pairing_eq_original M M hz hw,
    canonicalCompletedC3NormalizedFullWronskianOperatorKernel_eq_completed M hw hz]
  rfl

/-- Exact signed quadratic factorization in the ORIGINAL completed
Hilbert carrier. Both positive Gram channels remain; no subtraction is
discarded or replaced by a favorable metric. -/
theorem integral_pairing_chiral_difference (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    completedIntegralPairing M M z w /
        (2 * completedNativeOperatorCharacteristic z * conj (completedNativeOperatorCharacteristic w)) =
      Complex.I *
        (canonicalCompletedC3NormalizedFullWronskianPositiveChiralKernel M w z -
         canonicalCompletedC3NormalizedFullWronskianNegativeChiralKernel M w z) := by
  rw [integral_pairing_full_operator M hz hw]
  exact canonicalCompletedC3NormalizedFullWronskianKernel_div_eq_chiralDifference M hwF hzF

theorem mellin_response_signed_germ (M : ℕ) :
    mellinResponse M =ᶠ[nhds 0] canonicalCompletedC3FullWronskianChiralBalanceResponse M :=
  (mellin_response_eventuallyEq M).trans
    (canonicalCompletedC3FullWronskianChiralBalanceResponse_eventuallyEq_completed M).symm

end
end CarryCompletedPairing
