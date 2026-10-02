import GeometryOfNumbers.Analysis.CenterLegForm
import GeometryOfNumbers.Analysis.QuadraticCameraBracket

/-!
# Resolved energy of an indexed center-leg camera

The existing radii retain their local radial parameter, angle and plane state
through vector synthesis and energy readout. Only the resulting local energies
are summed. This is NOT the energy of a sum of vectors, nor the square of the
existing scalar camera bracket. The scalar crosswalk is channel by channel.
Common radial factorization requires only a nonzero parameter; its zero
criterion requires positive total input energy, without a separate size bound.
The repository supplies no canonical atlas/multibase carrier; this module
therefore stops at one indexed camera.
-/

namespace GeometryOfNumbers.Analysis

open Geometry

noncomputable section

def centerLegCameraEnergy (half : Nat) (q theta : Nat → ℝ)
    (v : Nat → RealPlaneState) : ℝ :=
  sumPositiveRadii half (fun r => realPlaneEnergy (centerLegForm (q r) (theta r) (v r)))

theorem centerLegCameraEnergy_eq_sum_local (half : Nat) (q theta : Nat → ℝ)
    (v : Nat → RealPlaneState) :
    centerLegCameraEnergy half q theta v =
      sumPositiveRadii half (fun r => realPlaneEnergy (centerLegForm (q r) (theta r) (v r))) := rfl

theorem centerLegCameraEnergy_eq_factor (half : Nat) (q theta : Nat → ℝ)
    (v : Nat → RealPlaneState) (hq : ∀ r, 1 ≤ r → r ≤ half → q r ≠ 0) :
    centerLegCameraEnergy half q theta v =
      sumPositiveRadii half (fun r => ((q r - 1) ^ 4 / q r ^ 2) * realPlaneEnergy (v r)) :=
  sumPositiveRadii_congr half _ _ (fun r hr hbound =>
    centerLegForm_energy_eq_fourth (q r) (theta r) (v r) (hq r hr hbound))

theorem centerLegCameraEnergy_angle_independent (half : Nat)
    (q theta₁ theta₂ : Nat → ℝ) (v : Nat → RealPlaneState) :
    centerLegCameraEnergy half q theta₁ v = centerLegCameraEnergy half q theta₂ v :=
  sumPositiveRadii_congr half _ _ (fun r _ _ =>
    centerLegForm_energy_angle_independent (q r) (theta₁ r) (theta₂ r) (v r))

theorem realPlaneEnergy_nonneg (v : RealPlaneState) : 0 ≤ realPlaneEnergy v :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem centerLegCameraEnergy_nonneg (half : Nat) (q theta : Nat → ℝ)
    (v : Nat → RealPlaneState) : 0 ≤ centerLegCameraEnergy half q theta v :=
  sumPositiveRadii_real_nonneg half _ (fun _ _ _ => realPlaneEnergy_nonneg _)

/-- No local energy can be canceled by the remaining channels. -/
theorem centerLegCameraEnergy_zero_iff_local_zero (half : Nat) (q theta : Nat → ℝ)
    (v : Nat → RealPlaneState) :
    centerLegCameraEnergy half q theta v = 0 ↔
      ∀ r, 1 ≤ r → r ≤ half → realPlaneEnergy (centerLegForm (q r) (theta r) (v r)) = 0 :=
  sumPositiveRadii_real_zero_iff half _ (fun _ _ _ => realPlaneEnergy_nonneg _)

theorem centerLegCameraEnergy_zero_iff (half : Nat) (q theta : Nat → ℝ)
    (v : Nat → RealPlaneState)
    (hq : ∀ r, 1 ≤ r → r ≤ half → 0 < q r)
    (hv : ∀ r, 1 ≤ r → r ≤ half → 0 < realPlaneEnergy (v r)) :
    centerLegCameraEnergy half q theta v = 0 ↔ ∀ r, 1 ≤ r → r ≤ half → q r = 1 := by
  rw [centerLegCameraEnergy_zero_iff_local_zero]
  constructor
  · intro hz r hr hbound
    exact (centerLegForm_energy_zero_iff (q r) (theta r) (v r)
      (hq r hr hbound) (hv r hr hbound)).1 (hz r hr hbound)
  · intro hz r hr hbound
    exact (centerLegForm_energy_zero_iff (q r) (theta r) (v r)
      (hq r hr hbound) (hv r hr hbound)).2 (hz r hr hbound)

theorem centerLegCameraEnergy_zero_pairs (q theta : Nat → ℝ) (v : Nat → RealPlaneState) :
    centerLegCameraEnergy 0 q theta v = 0 := rfl

/-- States and angles may vary independently while the radial factor is common. -/
theorem centerLegCameraEnergy_common_eq_factor (half : Nat) (q : ℝ)
    (theta : Nat → ℝ) (v : Nat → RealPlaneState) (hq : q ≠ 0) :
    centerLegCameraEnergy half (fun _ => q) theta v =
      ((q - 1) ^ 4 / q ^ 2) * sumPositiveRadii half (fun r => realPlaneEnergy (v r)) := by
  rw [centerLegCameraEnergy_eq_factor half _ theta v (fun _ _ _ => hq)]
  exact sumPositiveRadii_real_mul half _ _

theorem centerLegCameraEnergy_common_zero_iff (half : Nat) (q : ℝ)
    (theta : Nat → ℝ) (v : Nat → RealPlaneState) (hq : q ≠ 0)
    (hv : 0 < sumPositiveRadii half (fun r => realPlaneEnergy (v r))) :
    centerLegCameraEnergy half (fun _ => q) theta v = 0 ↔ q = 1 := by
  rw [centerLegCameraEnergy_common_eq_factor half q theta v hq]
  constructor
  · intro hz
    have hquotient := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hv)
    have hnumerator := (div_eq_zero_iff.mp hquotient).resolve_right
      (pow_ne_zero 2 hq)
    exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 4 ≠ 0)).mp hnumerator)
  · intro h
    simp [h]

/-- The unit-center scalar bracket is the coefficient of the local vector form. -/
theorem centerLegForm_energy_eq_unitBracket (q theta : ℝ) (v : RealPlaneState) :
    realPlaneEnergy (centerLegForm q theta v) =
      quadraticCenteredBracket 1 q ^ 2 * realPlaneEnergy v := by
  rw [centerLegForm_energy_eq_closed, quadraticCenteredBracket_eq_closed, one_mul]

theorem centerLegCameraEnergy_eq_sum_sq_brackets (half : Nat) (q theta : Nat → ℝ)
    (v : Nat → RealPlaneState) :
    centerLegCameraEnergy half q theta v =
      sumPositiveRadii half (fun r => quadraticCenteredBracket 1 (q r) ^ 2 * realPlaneEnergy (v r)) :=
  sumPositiveRadii_congr half _ _ (fun r _ _ =>
    centerLegForm_energy_eq_unitBracket (q r) (theta r) (v r))

/-- Equality of zero criteria under positive inputs, not equality of readouts. -/
theorem centerLegCameraEnergy_zero_iff_quadraticCameraBracket_zero (half : Nat)
    (q theta : Nat → ℝ) (v : Nat → RealPlaneState)
    (hq : ∀ r, 1 ≤ r → r ≤ half → 0 < q r)
    (hv : ∀ r, 1 ≤ r → r ≤ half → 0 < realPlaneEnergy (v r)) :
    centerLegCameraEnergy half q theta v = 0 ↔ quadraticCameraBracket half 1 q = 0 :=
  (centerLegCameraEnergy_zero_iff half q theta v hq hv).trans
    (quadraticCameraBracket_zero_iff half (center := 1) (by norm_num) q hq).symm

theorem centerLegCameraEnergy_criticalSeed_eq_mass (half b k : Nat) (hb : 0 < b)
    (q theta : Nat → ℝ) (hq : ∀ r, 1 ≤ r → r ≤ half → q r ≠ 0) :
    centerLegCameraEnergy half q theta (fun _ => realCriticalDepthSeed b k hb) =
      realDepthMass b k hb * sumPositiveRadii half (fun r => (q r - 1) ^ 4 / q r ^ 2) := by
  rw [centerLegCameraEnergy_eq_factor half q theta _ hq]
  have hlocal := sumPositiveRadii_congr half
    (fun r => ((q r - 1) ^ 4 / q r ^ 2) * realPlaneEnergy (realCriticalDepthSeed b k hb))
    (fun r => realDepthMass b k hb * ((q r - 1) ^ 4 / q r ^ 2)) (fun r _ _ => by
      rw [realCriticalDepthSeed_energy]
      ring)
  rw [hlocal]
  exact sumPositiveRadii_real_mul half _ _

theorem centerLegCameraEnergy_criticalSeed_common_eq_mass (half b k : Nat) (hb : 0 < b)
    (q : ℝ) (theta : Nat → ℝ) (hq : q ≠ 0) :
    centerLegCameraEnergy half (fun _ => q) theta (fun _ => realCriticalDepthSeed b k hb) =
      ((q - 1) ^ 4 / q ^ 2) * (half : ℝ) * realDepthMass b k hb := by
  rw [centerLegCameraEnergy_common_eq_factor half q theta _ hq,
    sumPositiveRadii_real_constant, realCriticalDepthSeed_energy]
  ring

end

end GeometryOfNumbers.Analysis
