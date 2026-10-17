import PrimeClockSchur
import CanonicalComparison

/-! Test the completed, source-derived Schur candidate against the existing
canonical first-jet calibration. This reuses the earlier source certificate;
it does not claim a new theta estimate or a theory-wide no-go. -/
namespace CarryPrimeClock
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator CarryMaterialCentralProjectionComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Energy of the genuine first jet of the existing normalized physical
family, now explicitly realized by coherent prime synthesis plus full return. -/
theorem completed_prime_schur_firstJet_energy :
    ‖deriv carryMaterialCenteredState 0‖^2 =
      ‖centeredClock 0‖^2/(2*‖baseTwoCriticalCompleteSignal 0‖^2) := by
  have h := carryMaterialCenteredState_firstJet_energy
  change ‖deriv carryMaterialCenteredState 0‖^2 =
    (‖physicalClock 0‖^2-‖inner ℂ carryMaterialCentralUnit (physicalClock 0)‖^2)/
      (2*‖baseTwoCriticalCompleteSignal 0‖^2) at h
  rw [← carryMaterialCentralComplement_norm_sq] at h
  exact h

/-- The full tail and return have already been included in this test.
The candidate fails at h1, so its positive norm cannot be named that moment. -/
theorem completed_prime_schur_firstJet_gap :
    (1/1024:ℝ) < ‖centeredClock 0‖^2/(2*‖baseTwoCriticalCompleteSignal 0‖^2) -
      canonicalCompletedNativeLogDerivativeMoment 1 := by
  rw [← completed_prime_schur_firstJet_energy]
  exact material_centered_firstJet_gap

theorem completed_prime_schur_not_canonical_firstJet :
    ‖centeredClock 0‖^2/(2*‖baseTwoCriticalCompleteSignal 0‖^2) ≠
      canonicalCompletedNativeLogDerivativeMoment 1 := by
  rw [← completed_prime_schur_firstJet_energy]
  exact material_centered_firstJet_ne_canonical

end
end CarryPrimeClock
