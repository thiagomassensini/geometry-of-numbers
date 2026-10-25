import CarrySelfAdjointOperator.CompletedNativePrimosProjectiveMassCrosswalkAudit

/-!
# A fixed active readout is an affine fibre, not a linear source family

The existing polarized prime-atlas Pythagoras concerns two states realizing
one fixed set of active readouts. Applying it unchanged to every member of a
linear source family would include the zero input and force those active
readouts, their original provenance state, and the seeded Bessel energy to
vanish. This obstruction does not exclude a source-dependent projection; it
identifies an additional construction needed before any transport to Green.
-/
namespace CarryBinomialGreen
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
open CPFormal.Analytic.Cp

/-- The zero input tests the ORIGINAL fixed readout predicate. -/
theorem fixed_readouts_linear_family_zero
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) (N : ℕ)
    (F : (Fin N → ℂ) →ₗ[ℝ] PrimeCarryDefectGlobalHilbert)
    (hF : ∀ c, IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn M s S (F c))
    (p : Nat.Primes) (hp : p ∈ S) :
    finiteEnrichedNativeGpreLogJetGreenBulkReadout p M 1 (fun _ => 1) s = 0 := by
  have h := hF 0 p hp
  simpa only [map_zero, inner_zero_right] using h.symm

/-- Fixed-readout realization by a homogeneous source forces the active state
itself to vanish, in the already defined prime-carry Hilbert space. -/
theorem fixed_readouts_linear_family_active_zero
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) (N : ℕ)
    (F : (Fin N → ℂ) →ₗ[ℝ] PrimeCarryDefectGlobalHilbert)
    (hF : ∀ c, IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn M s S (F c)) :
    canonicalEnrichedPrimeCarryDefectProvenanceState M s S = 0 := by
  have h := canonicalProvenanceState_norm_sq_le_of_realizesOn M s S (F 0) (hF 0)
  rw [map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (canonicalEnrichedPrimeCarryDefectProvenanceState M s S)]

/-- The same check kills the original seeded Bessel ledger, with no changed
metric, source, normalization, or positivity hypothesis. -/
theorem fixed_readouts_linear_family_bessel_zero
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) (N : ℕ)
    (F : (Fin N → ℂ) →ₗ[ℝ] PrimeCarryDefectGlobalHilbert)
    (hF : ∀ c, IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn M s S (F c)) :
    finiteSeededTfvdBesselEnergy M s S = 0 := by
  rw [← canonicalEnrichedPrimeCarryDefectProvenanceState_norm_sq_eq_finiteSeededTfvdBesselEnergy,
    fixed_readouts_linear_family_active_zero M s S N F hF, norm_zero,
    zero_pow (by decide : 2 ≠ 0)]

/-- A nonzero active state rules out ONLY this unchanged affine-to-linear
identification; a genuine source-dependent projection remains open. -/
theorem no_fixed_readout_linear_family_of_active_ne_zero
    (M : ℕ) (s : ℂ) (S : Finset Nat.Primes) (N : ℕ)
    (hactive : canonicalEnrichedPrimeCarryDefectProvenanceState M s S ≠ 0)
    (F : (Fin N → ℂ) →ₗ[ℝ] PrimeCarryDefectGlobalHilbert) :
    ¬ (∀ c, IsCanonicalEnrichedPrimeCarryDefectReadoutRealizationOn M s S (F c)) := by
  intro hF
  exact hactive (fixed_readouts_linear_family_active_zero M s S N F hF)

end
end CarryBinomialGreen
