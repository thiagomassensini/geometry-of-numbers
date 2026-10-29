import CompletedSourceBridge

namespace CarryCommutatorControl
open CarrySelfAdjointOperator CarryNativeTfvd
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- This constant is derived from the ORIGINAL two normalized chiral amplitudes. -/
def chiralDifference : ℂ := 2 * Complex.I / (Real.sqrt 2 : ℂ)

/-- Existing completed response at the original radial address. -/
def responseWeight (k j : ℕ) : ℂ :=
  completedGreenNormalizedResponse completedNativeOperatorCharacteristic
    completedNativeOperatorBoundaryCompanion (canonicalCompletedC3RadialTiltPoint k j)

theorem chiral_difference_ne_zero : chiralDifference ≠ 0 := by
  unfold chiralDifference
  exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne')

theorem chiral_weight_difference (z : ℂ)
    (hF : completedNativeOperatorCharacteristic z ≠ 0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate z ≠ 0) :
    completedNativeNormalizedPositiveChiralAmplitude z -
      completedNativeNormalizedPositiveChiralAmplitude z *
        completedNativeHermiteBiehlerChiralQuotient z = chiralDifference := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hr : completedNativeNormalizedPositiveChiralAmplitude z *
      completedNativeHermiteBiehlerChiralQuotient z =
      canonicalCompletedC3FullWronskianChiralNormalization z *
        completedNativeNegativeHermiteBiehlerCoordinate z := by
    unfold completedNativeNormalizedPositiveChiralAmplitude completedNativeHermiteBiehlerChiralQuotient
    field_simp [hP]
  rw [hr]
  unfold completedNativeNormalizedPositiveChiralAmplitude
  rw [← mul_sub]
  have hd : completedNativePositiveHermiteBiehlerCoordinate z -
      completedNativeNegativeHermiteBiehlerCoordinate z =
      2 * Complex.I * completedNativeOperatorCharacteristic z := by
    unfold completedNativePositiveHermiteBiehlerCoordinate completedNativeNegativeHermiteBiehlerCoordinate
    ring
  rw [hd]
  unfold canonicalCompletedC3FullWronskianChiralNormalization chiralDifference
  field_simp [hF, hs]

/-- The common variable amplitude is exactly the old logarithmic response. -/
theorem incident_amplitude_response (z : ℂ)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeNormalizedPositiveChiralAmplitude z =
      (2 * completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z + Complex.I) / (Real.sqrt 2 : ℂ) := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  unfold completedNativeNormalizedPositiveChiralAmplitude
    canonicalCompletedC3FullWronskianChiralNormalization
    completedNativePositiveHermiteBiehlerCoordinate completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  field_simp [hF, hs]

theorem radial_weight_difference (k j : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j) ≠ 0)
    (hP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j) ≠ 0) :
    incidentWeight k j - returnedWeight k j = chiralDifference :=
  chiral_weight_difference _ hF hP

/-- Regularity is proved upstream on every finite prefix; it is not a moment sign. -/
theorem radial_weight_difference_eventually (N : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ j : ℕ, j < N →
      incidentWeight k j - returnedWeight k j = chiralDifference := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular N] with k hk
  intro j hj
  exact radial_weight_difference k j (hk ⟨j,hj⟩).2.1 (hk ⟨j,hj⟩).2.2

end
end CarryCommutatorControl
