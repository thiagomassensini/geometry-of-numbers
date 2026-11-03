import SigmaZeroObstruction
import CarrySelfAdjointOperator.CompletedNativeChiralEvenBoundarySplit
import CarrySelfAdjointOperator.PrimeDepthGeometricMomentRecurrence

/-!
# Exact material boundary to central sigma-Hankel seam

This module transports the already-defined raw even-dimensional limiting-face energy to the
original central sigma matrices. It keeps the source parity phases and the two distinct Hankel
channels. It does not identify this limiting-face form with a finite-step storage energy or
assert a sign for either channel.
-/

open CarrySelfAdjointOperator CarrySigmaSource CarryMovingSigma CarryMomentLogConvex
open scoped BigOperators ComplexConjugate Matrix
noncomputable section
set_option autoImplicit false

namespace CarrySigmaObstruction

/-- Real readout of a real matrix against the complete Hermitian cross terms of a complex
boundary vector. -/
def materialHankelReadout {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℂ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, M i j * (conj (x i) * x j).re

/-- The raw even-dimensional native limiting-face energy is the direct sum of the original
central sigma Hankel readouts, after the source-defined parity phases. The unshifted channel
uses `sigmaMatrix 0 0`; the shifted channel uses `sigmaMatrix 0 1`. -/
theorem nativeSourceBoundaryEnergy_even_split_sigmaMatrix
    (n : ℕ) (x : Fin (2 * n) → ℂ) :
    nativeSourceFiniteBoundaryEnergy (2 * n) x = 4 *
      (materialHankelReadout (sigmaMatrix 0 0 n)
          (nativeSourceEvenBoundaryPhase n x) +
        materialHankelReadout (sigmaMatrix 0 1 n)
          (nativeSourceOddBoundaryPhase n x)) := by
  rw [nativeSourceFiniteBoundaryEnergy_even_split]
  have hmoment : primeDepthGeometricMoment =
      fun k : ℕ => completedSigmaLogJet 0 k := by
    funext k
    rw [primeDepthGeometricMoment_eq_canonical,
      ← sigma_log_jet_center_eq_canonical]
  simp_rw [hmoment, materialHankelReadout, sigmaMatrix, sourceMomentMatrix]
  simp

#print axioms nativeSourceBoundaryEnergy_even_split_sigmaMatrix

end CarrySigmaObstruction
end
