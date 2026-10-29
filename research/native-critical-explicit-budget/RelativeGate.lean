import TenCriticalTransfer
import GeneralBudget

namespace CarryExplicitBudget
open CarrySelfAdjointOperator CarryDirectAnchor CarryVariationalSchur CarryOddEnergy CarrySummableRadial
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- A relative budget criterion for any finite odd source family. The old
block need only be invertible, and every error still belongs to the original
fully synthesized physical sources. This is a sufficient condition, not an
assertion that the condition holds in all orders. -/
theorem finite_odd_critical_anchor_of_relative_budget
    (n k : ℕ) (z : Fin n → ℝ) (rho : ℝ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n))
    (hk : oddGridCutoff (Finset.range (n+1)) ≤ k)
    (hrho : rho < 1)
    (htrial : 0 < finiteSourceEnergy (n+1) (trialFin n z) k)
    (hrelative :
      (sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 n z ⬝ᵥ
        ((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment 1 n)⁻¹ *ᵥ
          sourceTrialResidual canonicalCompletedNativeLogDerivativeMoment 1 n z)) +
      physicalFiniteError (n+1) (trialFin n z) k +
      2*physicalFiniteError (n+1) (criticalFin n) k ≤
        rho*finiteSourceEnergy (n+1) (trialFin n z) k) :
    physicalFiniteError (n+1) (criticalFin n) k <
      finiteSourceEnergy (n+1) (criticalFin n) k := by
  have ht := finite_critical_transfer n k z hA hk
  have hp : rho*finiteSourceEnergy (n+1) (trialFin n z) k <
      finiteSourceEnergy (n+1) (trialFin n z) k := by nlinarith
  linarith

end
end CarryExplicitBudget
