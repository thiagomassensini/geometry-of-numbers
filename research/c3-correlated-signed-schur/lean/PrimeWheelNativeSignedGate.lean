import ResidualTest

/-!
The exact, physical signed remainder is the surviving Schur energy after
the old positive head has been removed. The positivity criterion below
does not identify camera independence with positivity: it isolates the
necessary RETURN-DOMINANCE obligation on the true original source.

No prime wheel Gram, fitted measure, or prescribed moment eigenvalue is
substituted into the physical carrier.
-/
namespace CarryWheelNativeSignedGate
open CarryReturnDeflation CarrySelfAdjointOperator ChiralReturn
open CarryPositiveSquare NativeMomentOrthogonalization GeometryOfNumbers.Analysis
open Filter Topology
open scoped InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- Exact signed residual in the original native return carrier. -/
theorem physical_remaining_pair_self_re (k N : ℕ) (c : Fin N → ℂ) :
    (remainingPair k N c c).re =
      ‖remainingIncident k N c‖^2 - ‖nativeOut k N c‖^2 := by
  simp only [remainingPair, Complex.sub_re, physical_inner_self_re]

/-- The necessary local criterion is not merely an independent channel:
its returned energy must not exceed its still-unresolved incident energy. -/
theorem critical_schur_remainder_nonneg_of_return_dominance
    (s : Fin 2) (n k : ℕ)
    (hdeficit : 0 < oneDeficit k)
    (hdom :
      ‖nativeOut k (2*(n+1))
        (nativeSourceChiralJetInput (n+1) k (nativeResidualBoundary s n))‖^2 ≤
      ‖remainingIncident k (2*(n+1))
        (nativeSourceChiralJetInput (n+1) k (nativeResidualBoundary s n))‖^2) :
    0 ≤ (jetSchurRemainder (n+1) k
        (nativeResidualBoundary s n) (nativeResidualBoundary s n)).re := by
  unfold jetSchurRemainder jetRemainingPair
  rw [Complex.div_ofReal_re, physical_remaining_pair_self_re]
  exact div_nonneg (sub_nonneg.mpr hdom) hdeficit.le

/-- An eventual dominance on the actual odd Schur residual implies
a nonnegative odd pivot. This has no preceding pivot hypothesis because
the old even-head is exactly orthogonal to that odd source. -/
theorem native_odd_pivot_nonneg_of_eventual_return_dominance
    (n : ℕ)
    (hdom : ∀ᶠ k : ℕ in atTop,
      ‖nativeOut k (2*(n+1))
        (nativeSourceChiralJetInput (n+1) k (nativeResidualBoundary 1 n))‖^2 ≤
      ‖remainingIncident k (2*(n+1))
        (nativeSourceChiralJetInput (n+1) k (nativeResidualBoundary 1 n))‖^2) :
    0 ≤ carryPairingPivot
        (hankelPairing (fun j => canonicalCompletedNativeLogDerivativeMoment (j+1))) n := by
  have hremain : ∀ᶠ k : ℕ in atTop,
      0 ≤ (jetSchurRemainder (n+1) k
        (nativeResidualBoundary 1 n) (nativeResidualBoundary 1 n)).re := by
    filter_upwards [oneDeficit_eventually_pos, hdom] with k hk hd
    exact critical_schur_remainder_nonneg_of_return_dominance 1 n k hk hd
  have hlimit := ge_of_tendsto (pr41_odd_remaining_energy_tendsto n) hremain
  linarith

/-- Even sector: old-prefix pivots are used only to identify the genuine
Schur-orthogonal input, never to manufacture positivity of the new pivot. -/
theorem native_even_pivot_nonneg_of_eventual_return_dominance
    (n : ℕ) (hn : 0 < n)
    (hp : ∀ r < n,
      carryPairingPivot (hankelPairing canonicalCompletedNativeLogDerivativeMoment) r ≠ 0)
    (hdom : ∀ᶠ k : ℕ in atTop,
      ‖nativeOut k (2*(n+1))
        (nativeSourceChiralJetInput (n+1) k (nativeResidualBoundary 0 n))‖^2 ≤
      ‖remainingIncident k (2*(n+1))
        (nativeSourceChiralJetInput (n+1) k (nativeResidualBoundary 0 n))‖^2) :
    0 ≤ carryPairingPivot
      (hankelPairing canonicalCompletedNativeLogDerivativeMoment) n := by
  have hremain : ∀ᶠ k : ℕ in atTop,
      0 ≤ (jetSchurRemainder (n+1) k
        (nativeResidualBoundary 0 n) (nativeResidualBoundary 0 n)).re := by
    filter_upwards [oneDeficit_eventually_pos, hdom] with k hk hd
    exact critical_schur_remainder_nonneg_of_return_dominance 0 n k hk hd
  have hlimit := ge_of_tendsto (pr41_even_remaining_energy_tendsto n hn hp) hremain
  linarith

end
end CarryWheelNativeSignedGate
