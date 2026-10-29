import PrimeProjection
import CarrySelfAdjointOperator.NativeRealFirstQuadratureNaturality

/-! Apply the SAME extraction to both full legs; retain both signed residuals.
This does not identify a prime-atlas projection with the native chiral return. -/
namespace CarrySourcePrime
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
open CarrySelfAdjointOperator.RealQuadrature
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false

def quadratureProjection (S : Finset Nat.Primes) :
    Space PrimeCarryDefectGlobalHilbert →ₗ[ℝ] Space PrimeCarryDefectGlobalHilbert :=
  lift (primeProjection S)

theorem quadrature_projection_rotation (S : Finset Nat.Primes)
    (X : Space PrimeCarryDefectGlobalHilbert) :
    quadratureProjection S (J X)=J (quadratureProjection S X) := lift_J _ _

/-- Both quadratures and both independent arguments, before any diagonal. -/
theorem quadrature_projection_pairing (S : Finset Nat.Primes)
    (X Y : Space PrimeCarryDefectGlobalHilbert) :
    inner ℝ X Y=inner ℝ (quadratureProjection S X) (quadratureProjection S Y)+
      inner ℝ (X-quadratureProjection S X) (Y-quadratureProjection S Y) := by
  have h1 := prime_projection_polarized_pythagoras S X.fst Y.fst
  have h2 := prime_projection_polarized_pythagoras S X.snd Y.snd
  change inner ℝ X.fst Y.fst+inner ℝ X.snd Y.snd=
    (inner ℝ (primeProjection S X.fst) (primeProjection S Y.fst)+
      inner ℝ (primeProjection S X.snd) (primeProjection S Y.snd))+
    (inner ℝ (X.fst-primeProjection S X.fst) (Y.fst-primeProjection S Y.fst)+
      inner ℝ (X.snd-primeProjection S X.snd) (Y.snd-primeProjection S Y.snd))
  linarith

/-- The rotation-associated polarized form is conserved as well. -/
theorem quadrature_projection_rotation_pairing (S : Finset Nat.Primes)
    (X Y : Space PrimeCarryDefectGlobalHilbert) :
    inner ℝ (J X) Y=
      inner ℝ (J (quadratureProjection S X)) (quadratureProjection S Y)+
      inner ℝ (J (X-quadratureProjection S X)) (Y-quadratureProjection S Y) := by
  have h := quadrature_projection_pairing S (J X) Y
  simpa only [quadrature_projection_rotation, map_sub] using h

/-- Faithful posterior packaging of the two preceding identities. -/
theorem quadrature_projection_complex_pairing (S : Finset Nat.Primes)
    (X Y : Space PrimeCarryDefectGlobalHilbert) :
    inner ℂ (pack X) (pack Y)=
      inner ℂ (pack (quadratureProjection S X)) (pack (quadratureProjection S Y))+
      inner ℂ (pack (X-quadratureProjection S X)) (pack (Y-quadratureProjection S Y)) := by
  simp only [pack_inner]
  rw [quadrature_projection_pairing S X Y,quadrature_projection_rotation_pairing S X Y]
  push_cast
  ring

/-- A positive extraction splits the SIGNED form into two signed terms.
Neither the incident nor the returned complement is discarded. -/
theorem complete_signed_readout_split (S : Finset Nat.Primes)
    (I R I' R' : Space PrimeCarryDefectGlobalHilbert) :
    inner ℂ (pack I) (pack I')-inner ℂ (pack R) (pack R')=
      (inner ℂ (pack (quadratureProjection S I)) (pack (quadratureProjection S I'))-
        inner ℂ (pack (quadratureProjection S R)) (pack (quadratureProjection S R')))+
      (inner ℂ (pack (I-quadratureProjection S I)) (pack (I'-quadratureProjection S I'))-
        inner ℂ (pack (R-quadratureProjection S R)) (pack (R'-quadratureProjection S R'))) := by
  rw [quadrature_projection_complex_pairing S I I',quadrature_projection_complex_pairing S R R']
  ring

end
end CarrySourcePrime
