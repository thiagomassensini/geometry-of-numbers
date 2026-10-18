import CanonicalClockGap
import OddPhysicalTwelve

namespace CarryStructuralKrylov
open GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator CarryReturnCompatibility CarryCorrectedGreenPorts
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false

/-- These remain the original TWO six-by-six blocks, now explicitly read as
moments of the local full canonical response; no candidate vectors are fitted. -/
theorem regression_H6_K6 :
    (GeometryOfNumbers.Analysis.hankelGram baseTwoCanonicalMomentSequence 6).PosDef ∧
      (GeometryOfNumbers.Analysis.shiftedHankel baseTwoCanonicalMomentSequence 6).PosDef := by
  rw [canonical_moments_eq_native]
  constructor
  · convert CarrySixthEven.even_source_six_posDef using 1
    ext i j
    simp [GeometryOfNumbers.Analysis.hankelGram, sourceMomentMatrix, CarryCriticalSource.h]
  · convert CarrySixthOdd.odd_source_six_posDef using 1
    ext i j
    simp [GeometryOfNumbers.Analysis.shiftedHankel, sourceMomentMatrix, CarryCriticalSource.h]

/-- The already-certified physical family retains all prefixes and both
arguments, and is kept distinct from the material-clock candidate just excluded. -/
theorem regression_twelve_nested :
    ∃ v : Fin 12 → CanonicalCompletedNativeChiralCauchyCarrier,
      ∀ (N : ℕ) (hN : N ≤ 12) (a b : Fin N),
        inner ℂ (fullSourceJet v (Fin.castLE hN a))
          (fullSourceJet v (Fin.castLE hN b)) =
            polarizedGreenMomentCoefficient baseTwoCanonicalMomentSequence a.val b.val := by
  rw [canonical_moments_eq_native]
  exact CarrySixthOdd.canonical_twelve_nested_realization

end
end CarryStructuralKrylov
