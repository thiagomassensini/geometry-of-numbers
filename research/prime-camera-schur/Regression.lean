import LiteralCameraCanary
import PrimeClockGreenTransport

namespace CarryPrimeClock
open CarrySelfAdjointOperator GeometryOfNumbers.Analysis
open GeometryOfNumbers.Analysis.BaseTwoCompletion
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- An empty interior prefix still keeps the original full clock return. -/
theorem regression_empty_head_return (t : ℝ) :
    (physicalClockHead 0 t).snd.snd = globalClockReturn t := by
  simp [physicalClockHead, edgeInjection, returnInjection]

/-- The same concrete encoder/decoder recovers the full physical Schur
forcing at the center, rather than a state chosen from a target Gram. -/
theorem regression_literal_forcing :
    carryMaterialCentralComplement
      (decodedCompleteClock (finiteLiteralCameraMatrix 1 twoPrimeCameras) 0) =
        carryMaterialClockCentralForcing := by
  rw [literal_decoded_clock_eq]
  exact centeredClock_zero_eq_forcing

/-- A diagonal test without division by u-t: the hidden Green balance
remains exactly equal to the full balance on this diagonal. -/
theorem regression_green_diagonal :
    ∃ U : Set ℝ, IsOpen U ∧ (0:ℝ) ∈ U ∧ ∀ t ∈ U,
      carryMaterialPairGreen (primeReducedPair 0 t) (primeReducedPair 2 t) =
        carryMaterialPairGreen (carryMaterialPairComplement (primeReducedPair 0 t))
          (carryMaterialPairComplement (primeReducedPair 2 t)) := by
  obtain ⟨U,ho,hz,h⟩ := completed_prime_green_real_residual
  refine ⟨U,ho,hz,?_⟩
  intro t ht
  have he := h 0 2 t ht t ht
  simp only [sub_self, Complex.ofReal_zero, mul_zero, zero_mul] at he
  exact sub_eq_zero.mp he

end
end CarryPrimeClock
