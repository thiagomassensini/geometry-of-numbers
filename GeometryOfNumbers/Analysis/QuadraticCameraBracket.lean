import GeometryOfNumbers.Geometry.OddCameraBracket
import GeometryOfNumbers.Analysis.QuadraticCenteredBracket

/-!
# Quadratic realization on the SAME positive-radius enumeration

The discrete camera precedes this module. Its radii label pairs; the values
q(r) are freely supplied, not selected by their labels. Each summand reuses
the existing local bracket. No equality identifying discrete observable
values with these reciprocal legs is assumed or claimed.
-/

namespace GeometryOfNumbers.Analysis

open Foundation Geometry

noncomputable section

theorem sumPositiveRadii_real_sub (half : ℕ) (f g : ℕ → ℝ) :
    sumPositiveRadii half (fun r => f r - g r) =
      sumPositiveRadii half f - sumPositiveRadii half g := by
  induction half with
  | zero => simp [sumPositiveRadii_zero]
  | succ half ih =>
    rw [sumPositiveRadii_succ, sumPositiveRadii_succ, sumPositiveRadii_succ, ih]
    ring

theorem sumPositiveRadii_real_constant (half : ℕ) (value : ℝ) :
    sumPositiveRadii half (fun _ => value) = (half : ℝ) * value := by
  induction half with
  | zero => simp [sumPositiveRadii_zero]
  | succ half ih =>
    rw [sumPositiveRadii_succ, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem sumPositiveRadii_real_mul (half : ℕ) (center : ℝ) (f : ℕ → ℝ) :
    sumPositiveRadii half (fun r => center * f r) = center * sumPositiveRadii half f := by
  induction half with
  | zero => simp [sumPositiveRadii_zero]
  | succ half ih =>
    rw [sumPositiveRadii_succ, sumPositiveRadii_succ, ih]
    ring

theorem sumPositiveRadii_real_nonneg (half : ℕ) (f : ℕ → ℝ)
    (hf : ∀ r, 1 ≤ r → r ≤ half → 0 ≤ f r) : 0 ≤ sumPositiveRadii half f := by
  induction half with
  | zero => exact le_refl 0
  | succ half ih =>
    rw [sumPositiveRadii_succ]
    exact add_nonneg
      (ih (fun r hr hbound => hf r hr (Nat.le_trans hbound (Nat.le_succ half))))
      (hf (half + 1) (by omega) (Nat.le_refl _))

theorem sumPositiveRadii_real_zero_iff (half : ℕ) (f : ℕ → ℝ)
    (hf : ∀ r, 1 ≤ r → r ≤ half → 0 ≤ f r) :
    sumPositiveRadii half f = 0 ↔ ∀ r, 1 ≤ r → r ≤ half → f r = 0 := by
  induction half with
  | zero =>
    constructor
    · intro _ r hr hbound
      omega
    · intro _
      rfl
  | succ half ih =>
    have hprevious := fun r hr hbound => hf r hr (Nat.le_trans hbound (Nat.le_succ half))
    have hp := sumPositiveRadii_real_nonneg half f hprevious
    have ht := hf (half + 1) (by omega) (Nat.le_refl _)
    rw [sumPositiveRadii_succ]
    constructor
    · intro hz
      have hzprevious : sumPositiveRadii half f = 0 := by linarith
      have hztop : f (half + 1) = 0 := by linarith
      have hpoint := (ih hprevious).1 hzprevious
      intro r hr hbound
      by_cases htop : r = half + 1
      · rw [htop]
        exact hztop
      · exact hpoint r hr (by omega)
    · intro hz
      rw [(ih hprevious).2 (fun r hr hbound =>
        hz r hr (Nat.le_trans hbound (Nat.le_succ half))),
        hz (half + 1) (by omega) (Nat.le_refl _), zero_add]

def quadraticCameraLegSum (half : ℕ) (center : ℝ) (q : ℕ → ℝ) : ℝ :=
  sumPositiveRadii half (fun r => quadraticLeftLeg center (q r) + quadraticRightLeg center (q r))

/-- Defined by the existing local brackets, never by a positive factorization. -/
def quadraticCameraBracket (half : ℕ) (center : ℝ) (q : ℕ → ℝ) : ℝ :=
  sumPositiveRadii half (fun r => quadraticCenteredBracket center (q r))

theorem quadraticCameraBracket_eq_legs_sub_centers
    (half : ℕ) (center : ℝ) (q : ℕ → ℝ) :
    quadraticCameraBracket half center q = quadraticCameraLegSum half center q -
      (2 * (half : ℝ)) * center := by
  unfold quadraticCameraBracket quadraticCameraLegSum
  have hlocal := sumPositiveRadii_congr half
    (fun r => quadraticCenteredBracket center (q r))
    (fun r => (quadraticLeftLeg center (q r) + quadraticRightLeg center (q r)) - 2 * center)
    (fun r _ _ => by unfold quadraticCenteredBracket realCenteredReadout; ring)
  rw [hlocal, sumPositiveRadii_real_sub, sumPositiveRadii_real_constant]
  ring

theorem quadraticCameraBracket_eq_closed (half : ℕ) (center : ℝ) (q : ℕ → ℝ) :
    quadraticCameraBracket half center q =
      center * sumPositiveRadii half (fun r => q r + (q r)⁻¹ - 2) := by
  unfold quadraticCameraBracket
  rw [sumPositiveRadii_congr half _ _ (fun r _ _ => quadraticCenteredBracket_eq_closed center (q r))]
  exact sumPositiveRadii_real_mul half center _

theorem quadraticCameraBracket_eq_factor (half : ℕ) (center : ℝ) (q : ℕ → ℝ)
    (hq : ∀ r, 1 ≤ r → r ≤ half → q r ≠ 0) :
    quadraticCameraBracket half center q =
      center * sumPositiveRadii half (fun r => (q r - 1) ^ 2 * (q r)⁻¹) := by
  unfold quadraticCameraBracket
  have hlocal := sumPositiveRadii_congr half
    (fun r => quadraticCenteredBracket center (q r))
    (fun r => center * ((q r - 1) ^ 2 * (q r)⁻¹)) (fun r hr hbound => by
      rw [quadraticCenteredBracket_eq_factor _ _ (hq r hr hbound)]
      ring)
  rw [hlocal]
  exact sumPositiveRadii_real_mul half center _

theorem quadraticCameraBracket_nonneg (half : ℕ) {center : ℝ} (hc : 0 < center)
    (q : ℕ → ℝ) (hq : ∀ r, 1 ≤ r → r ≤ half → 0 < q r) :
    0 ≤ quadraticCameraBracket half center q :=
  sumPositiveRadii_real_nonneg half _ (fun r hr hbound =>
    quadraticCenteredBracket_nonneg hc (hq r hr hbound))

theorem quadraticCameraBracket_zero_iff (half : ℕ) {center : ℝ} (hc : 0 < center)
    (q : ℕ → ℝ) (hq : ∀ r, 1 ≤ r → r ≤ half → 0 < q r) :
    quadraticCameraBracket half center q = 0 ↔ ∀ r, 1 ≤ r → r ≤ half → q r = 1 := by
  have hsum := sumPositiveRadii_real_zero_iff half
    (fun r => quadraticCenteredBracket center (q r))
    (fun r hr hbound => quadraticCenteredBracket_nonneg hc (hq r hr hbound))
  constructor
  · intro hz r hr hbound
    exact (quadraticCenteredBracket_zero_iff hc (hq r hr hbound)).1
      (hsum.1 hz r hr hbound)
  · intro hcentral
    exact hsum.2 (fun r hr hbound =>
      (quadraticCenteredBracket_zero_iff hc (hq r hr hbound)).2 (hcentral r hr hbound))

theorem quadraticCameraBracket_zero_pairs (center : ℝ) (q : ℕ → ℝ) :
    quadraticCameraBracket 0 center q = 0 := rfl

theorem quadraticCameraBracket_reflection (half : ℕ) (center : ℝ) (q : ℕ → ℝ) :
    quadraticCameraBracket half center (fun r => reciprocalReflection (q r)) =
      quadraticCameraBracket half center q :=
  sumPositiveRadii_congr half _ _ (fun r _ _ => quadraticCenteredBracket_reflection center (q r))

/-- A supplied Boolean mask can reflect ANY subset of the pairs independently. -/
def reflectCameraPairs (q : ℕ → ℝ) (mask : ℕ → Bool) (r : ℕ) : ℝ :=
  if mask r then reciprocalReflection (q r) else q r

theorem quadraticCameraBracket_independent_reflections
    (half : ℕ) (center : ℝ) (q : ℕ → ℝ) (mask : ℕ → Bool) :
    quadraticCameraBracket half center (reflectCameraPairs q mask) =
      quadraticCameraBracket half center q := by
  apply sumPositiveRadii_congr
  intro r _ _
  cases hm : mask r <;>
    simp [reflectCameraPairs, hm, quadraticCenteredBracket_reflection]

theorem quadraticCameraBracket_reflect_one_pair
    (half : ℕ) (center : ℝ) (q : ℕ → ℝ) (index : ℕ) :
    quadraticCameraBracket half center (reflectCameraPairs q (fun r => r == index)) =
      quadraticCameraBracket half center q :=
  quadraticCameraBracket_independent_reflections half center q _

/-- The camera's own explicit half supplies its capacity; no separate base is chosen. -/
def criticalQuadraticCameraBracket (half k : ℕ) (q : ℕ → ℝ) : ℝ :=
  quadraticCameraBracket half
    (realCriticalAmplitude (oddCameraCapacity half) k (oddCameraCapacity_pos half)) q

theorem criticalQuadraticCameraBracket_eq_sum_local (half k : ℕ) (q : ℕ → ℝ) :
    criticalQuadraticCameraBracket half k q = sumPositiveRadii half
      (fun r => criticalQuadraticBracket (oddCameraCapacity half) k (oddCameraCapacity_pos half) (q r)) := rfl

theorem criticalQuadraticCameraBracket_eq_closed (half k : ℕ) (q : ℕ → ℝ) :
    criticalQuadraticCameraBracket half k q =
      realCriticalAmplitude (oddCameraCapacity half) k (oddCameraCapacity_pos half) *
        sumPositiveRadii half (fun r => q r + (q r)⁻¹ - 2) :=
  quadraticCameraBracket_eq_closed half _ q

theorem criticalQuadraticCameraBracket_eq_factor (half k : ℕ) (q : ℕ → ℝ)
    (hq : ∀ r, 1 ≤ r → r ≤ half → q r ≠ 0) :
    criticalQuadraticCameraBracket half k q =
      realCriticalAmplitude (oddCameraCapacity half) k (oddCameraCapacity_pos half) *
        sumPositiveRadii half (fun r => (q r - 1) ^ 2 * (q r)⁻¹) :=
  quadraticCameraBracket_eq_factor half _ q hq

theorem criticalQuadraticCameraBracket_nonneg (half k : ℕ) (q : ℕ → ℝ)
    (hq : ∀ r, 1 ≤ r → r ≤ half → 0 < q r) :
    0 ≤ criticalQuadraticCameraBracket half k q :=
  quadraticCameraBracket_nonneg half
    (realCriticalAmplitude_pos _ _ (oddCameraCapacity_pos half)) q hq

theorem criticalQuadraticCameraBracket_zero_iff (half k : ℕ) (q : ℕ → ℝ)
    (hq : ∀ r, 1 ≤ r → r ≤ half → 0 < q r) :
    criticalQuadraticCameraBracket half k q = 0 ↔ ∀ r, 1 ≤ r → r ≤ half → q r = 1 :=
  quadraticCameraBracket_zero_iff half
    (realCriticalAmplitude_pos _ _ (oddCameraCapacity_pos half)) q hq

theorem criticalQuadraticCameraBracket_independent_reflections
    (half k : ℕ) (q : ℕ → ℝ) (mask : ℕ → Bool) :
    criticalQuadraticCameraBracket half k (reflectCameraPairs q mask) =
      criticalQuadraticCameraBracket half k q :=
  quadraticCameraBracket_independent_reflections half _ q mask

theorem criticalQuadraticCameraBracket_reflection (half k : ℕ) (q : ℕ → ℝ) :
    criticalQuadraticCameraBracket half k (fun r => reciprocalReflection (q r)) =
      criticalQuadraticCameraBracket half k q :=
  quadraticCameraBracket_reflection half _ q

theorem criticalQuadraticCameraBracket_zero_pairs (k : ℕ) (q : ℕ → ℝ) :
    criticalQuadraticCameraBracket 0 k q = 0 := rfl

/-- EACH pair preserves the same central mass; there is no sum of masses here. -/
theorem criticalQuadraticCameraPair_product (half k : ℕ) (q : ℕ → ℝ)
    (r : ℕ) (_hr : 1 ≤ r) (_hbound : r ≤ half) (hq : q r ≠ 0) :
    criticalQuadraticLeftLeg (oddCameraCapacity half) k (oddCameraCapacity_pos half) (q r) *
      criticalQuadraticRightLeg (oddCameraCapacity half) k (oddCameraCapacity_pos half) (q r) =
        realDepthMass (oddCameraCapacity half) k (oddCameraCapacity_pos half) :=
  criticalQuadraticLegs_product _ _ _ _ hq

/-- Support records why the same k is used. It does not prove the algebra;
the previously derived mass supplies the amplitude of every local pair. -/
theorem balancedCarryDepth_quadraticCamera_provenance (half n k : ℕ)
    (hdepth : HasIntegerCarryDepthAtLeast (oddCameraCapacity half)
      (balancedCarryCenter (oddCameraCapacity half) n (oddCameraCapacity_isOdd half)) k)
    (q : ℕ → ℝ) (hq : ∀ r, 1 ≤ r → r ≤ half → 0 < q r) :
    HasIntegerCarryDepthAtLeast (oddCameraCapacity half)
      ((n : Int) - balancedCarryOffset (oddCameraCapacity half) n (oddCameraCapacity_isOdd half)) k ∧
      (canonicalResidualDepthMass (oddCameraCapacity half) k (oddCameraCapacity_pos half)).numerator = 1 ∧
      (canonicalResidualDepthMass (oddCameraCapacity half) k (oddCameraCapacity_pos half)).denominator =
        oddCameraCapacity half ^ k ∧
      (∀ r, 1 ≤ r → r ≤ half →
        criticalQuadraticLeftLeg (oddCameraCapacity half) k (oddCameraCapacity_pos half) (q r) *
          criticalQuadraticRightLeg (oddCameraCapacity half) k (oddCameraCapacity_pos half) (q r) =
            realizeCountingShare (canonicalResidualDepthMass (oddCameraCapacity half) k
              (oddCameraCapacity_pos half))) ∧
      criticalQuadraticCameraBracket half k q = sumPositiveRadii half
        (fun r => criticalQuadraticBracket (oddCameraCapacity half) k (oddCameraCapacity_pos half) (q r)) := by
  have hp := balancedCarry_depth_and_mass_at_same_index (oddCameraCapacity half) n k
    (oddCameraCapacity_isOdd half) hdepth
  exact ⟨hp.1, hp.2.1, hp.2.2,
    fun r hr hbound => criticalQuadraticCameraPair_product half k q r hr hbound
      (ne_of_gt (hq r hr hbound)), rfl⟩

end

end GeometryOfNumbers.Analysis
