import PrimeWheelNativeSignedGate

/-!
# Actual completed chiral return: exact quotient-variation formula

The return is NOT a projector that by definition kills previously inherited
prime-camera directions. It multiplies the existing original Cauchy basis
by the completed Hermite-Biehler quotient Q(z_i).

Subtracting the old anchor return Q(z_0) gives exactly a variation of the
same quotient across the CURRENT jet grid. This is the concrete signed
channel whose norm must be compared with the unresolved incidence.

No moments are used to construct the source, norm or multiplier.
-/

namespace CarryWheelNativeSignedGate

open CarryReturnDeflation CarrySelfAdjointOperator ChiralReturn CarryPositiveSquare
open scoped BigOperators InnerProductSpace ComplexConjugate

noncomputable section

def quotientVariationCoefficient (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (i : Fin N) : ℂ :=
  c i * (completedNativeHermiteBiehlerChiralQuotient
    (canonicalCompletedC3RadialTiltPoint k i) - oneReturn k)

/-- The original physical output after deflation of the old head is
exactly the incident Cauchy synthesis with Q(z_i)-Q(z_0). -/
theorem nativeOut_eq_quotientVariation (k N : ℕ) (c : Fin N → ℂ) :
    nativeOut k N c =
      radialIncidentSynthesis k N (quotientVariationCoefficient k c) := by
  calc
    nativeOut k N c =
      radialIncidentSynthesis k N
        (fun i => c i * completedNativeHermiteBiehlerChiralQuotient
          (canonicalCompletedC3RadialTiltPoint k i)) -
        oneReturn k • radialIncidentSynthesis k N c := by
      simp only [nativeOut, LinearMap.sub_apply, LinearMap.smul_apply]
      rw [radialReturnedSynthesis_eq_incident_multiply]
    _ = radialIncidentSynthesis k N (quotientVariationCoefficient k c) := by
      rw [← map_smul, ← map_sub]
      congr 1
      funext i
      simp [quotientVariationCoefficient]
      ring

/-- The old first camera is removed exactly; nothing asserts cancellation
for every later or genuinely primitive input. -/
theorem quotientVariationCoefficient_zero (k N : ℕ)
    (hN : 0 < N) (c : Fin N → ℂ) :
    quotientVariationCoefficient k c ⟨0,hN⟩ = 0 := by
  simp [quotientVariationCoefficient, oneReturn]

end
end CarryWheelNativeSignedGate
