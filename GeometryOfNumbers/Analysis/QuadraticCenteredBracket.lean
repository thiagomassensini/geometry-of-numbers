import GeometryOfNumbers.Analysis.QuadraticReflection
import Mathlib.Tactic.FieldSimp

/-!
# The local bracket as an additive readout of reciprocal legs

The legs conserve a product; the centered readout tests a sum. Its mismatch
is derived, not used to select the earlier amplitude or exponent. This is a
local scalar bracket, not a historical camera or aggregated bracket.
-/

namespace GeometryOfNumbers.Analysis

open Foundation Geometry

noncomputable section

def realCenteredReadout (left center right : ℝ) : ℝ := left - 2 * center + right

theorem realCenteredReadout_swap (left center right : ℝ) :
    realCenteredReadout right center left = realCenteredReadout left center right := by
  unfold realCenteredReadout
  ring

/-- The additive construction conserves a sum, unlike the reciprocal construction. -/
theorem realCenteredReadout_additiveLegs (center offset : ℝ) :
    realCenteredReadout (center - offset) center (center + offset) = 0 := by
  unfold realCenteredReadout
  ring

def quadraticCenteredBracket (center q : ℝ) : ℝ :=
  realCenteredReadout (quadraticLeftLeg center q) center (quadraticRightLeg center q)

theorem quadraticCenteredBracket_eq_closed (center q : ℝ) :
    quadraticCenteredBracket center q = center * (q + q⁻¹ - 2) := by
  unfold quadraticCenteredBracket realCenteredReadout quadraticLeftLeg
    quadraticRightLeg reciprocalReflection
  ring

theorem quadraticCenteredBracket_eq_factor (center q : ℝ) (hq : q ≠ 0) :
    quadraticCenteredBracket center q = center * (q - 1) ^ 2 * q⁻¹ := by
  rw [quadraticCenteredBracket_eq_closed]
  field_simp
  ring

theorem quadraticCenteredBracket_nonneg {center q : ℝ}
    (hc : 0 < center) (hq : 0 < q) : 0 ≤ quadraticCenteredBracket center q := by
  rw [quadraticCenteredBracket_eq_factor _ _ (ne_of_gt hq)]
  exact mul_nonneg (mul_nonneg (le_of_lt hc) (sq_nonneg _)) (le_of_lt (inv_pos.mpr hq))

theorem quadraticCenteredBracket_at_one (center : ℝ) :
    quadraticCenteredBracket center 1 = 0 := by
  rw [quadraticCenteredBracket_eq_closed]
  ring

theorem quadraticCenteredBracket_zero_iff {center q : ℝ}
    (hc : 0 < center) (hq : 0 < q) : quadraticCenteredBracket center q = 0 ↔ q = 1 := by
  constructor
  · intro hz
    rw [quadraticCenteredBracket_eq_factor _ _ (ne_of_gt hq)] at hz
    have hprod := (mul_eq_zero.mp hz).resolve_right (inv_ne_zero (ne_of_gt hq))
    have hsquare := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hc)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro h
    rw [h]
    exact quadraticCenteredBracket_at_one center

theorem quadraticCenteredBracket_pos {center q : ℝ}
    (hc : 0 < center) (hq : 0 < q) (hcentral : q ≠ 1) :
    0 < quadraticCenteredBracket center q := by
  rw [quadraticCenteredBracket_eq_factor _ _ (ne_of_gt hq)]
  exact mul_pos (mul_pos hc (sq_pos_of_ne_zero (sub_ne_zero.mpr hcentral))) (inv_pos.mpr hq)

/-- Reflection invariance follows from swapping the constructed legs. -/
theorem quadraticCenteredBracket_reflection (center q : ℝ) :
    quadraticCenteredBracket center (reciprocalReflection q) =
      quadraticCenteredBracket center q := by
  unfold quadraticCenteredBracket
  rw [quadraticLeftLeg_reflection, quadraticRightLeg_reflection]
  exact realCenteredReadout_swap _ _ _

/-- Zero inversion in Lean is total, but it does not model a nonzero reciprocal pair. -/
theorem quadraticCenteredBracket_zero_parameter (center : ℝ) :
    quadraticCenteredBracket center 0 = -2 * center := by
  rw [quadraticCenteredBracket_eq_closed]
  simp only [inv_zero, add_zero, zero_sub]
  ring

def criticalQuadraticBracket (b k : ℕ) (hb : 0 < b) (q : ℝ) : ℝ :=
  quadraticCenteredBracket (realCriticalAmplitude b k hb) q

theorem criticalQuadraticBracket_eq_readout (b k : ℕ) (hb : 0 < b) (q : ℝ) :
    criticalQuadraticBracket b k hb q =
      realCenteredReadout (criticalQuadraticLeftLeg b k hb q) (realCriticalAmplitude b k hb)
        (criticalQuadraticRightLeg b k hb q) := rfl

theorem criticalQuadraticBracket_eq_closed (b k : ℕ) (hb : 0 < b) (q : ℝ) :
    criticalQuadraticBracket b k hb q = realCriticalAmplitude b k hb * (q + q⁻¹ - 2) :=
  quadraticCenteredBracket_eq_closed _ _

theorem criticalQuadraticBracket_eq_factor
    (b k : ℕ) (hb : 0 < b) (q : ℝ) (hq : q ≠ 0) :
    criticalQuadraticBracket b k hb q = realCriticalAmplitude b k hb * (q - 1) ^ 2 * q⁻¹ :=
  quadraticCenteredBracket_eq_factor _ _ hq

theorem criticalQuadraticBracket_nonneg
    (b k : ℕ) (hb : 0 < b) {q : ℝ} (hq : 0 < q) :
    0 ≤ criticalQuadraticBracket b k hb q :=
  quadraticCenteredBracket_nonneg (realCriticalAmplitude_pos b k hb) hq

theorem criticalQuadraticBracket_zero_iff
    (b k : ℕ) (hb : 0 < b) {q : ℝ} (hq : 0 < q) :
    criticalQuadraticBracket b k hb q = 0 ↔ q = 1 :=
  quadraticCenteredBracket_zero_iff (realCriticalAmplitude_pos b k hb) hq

theorem criticalQuadraticBracket_pos
    (b k : ℕ) (hb : 0 < b) {q : ℝ} (hq : 0 < q) (hcentral : q ≠ 1) :
    0 < criticalQuadraticBracket b k hb q :=
  quadraticCenteredBracket_pos (realCriticalAmplitude_pos b k hb) hq hcentral

theorem criticalQuadraticBracket_reflection (b k : ℕ) (hb : 0 < b) (q : ℝ) :
    criticalQuadraticBracket b k hb (reciprocalReflection q) = criticalQuadraticBracket b k hb q :=
  quadraticCenteredBracket_reflection _ _

theorem criticalQuadraticBracket_zero_depth (b : ℕ) (hb : 0 < b) (q : ℝ) :
    criticalQuadraticBracket b 0 hb q = q + q⁻¹ - 2 := by
  rw [criticalQuadraticBracket_eq_closed, realCriticalAmplitude_zero, one_mul]

theorem criticalQuadraticBracket_capacity_one (k : ℕ) (q : ℝ) :
    criticalQuadraticBracket 1 k Nat.zero_lt_one q = q + q⁻¹ - 2 := by
  rw [criticalQuadraticBracket_eq_closed, realCriticalAmplitude_one, one_mul]

/-- The offset exposes the same supported index; the legs preserve its earlier
formal mass, and the bracket reads those legs without changing that mass. -/
theorem balancedCarryDepth_quadraticReflection_provenance
    (b n k : ℕ) (hodd : IsOddCapacity b)
    (hdepth : HasIntegerCarryDepthAtLeast b (balancedCarryCenter b n hodd) k)
    (q : ℝ) (hq : q ≠ 0) :
    HasIntegerCarryDepthAtLeast b ((n : Int) - balancedCarryOffset b n hodd) k ∧
      (canonicalResidualDepthMass b k (oddCapacity_pos hodd)).numerator = 1 ∧
      (canonicalResidualDepthMass b k (oddCapacity_pos hodd)).denominator = b ^ k ∧
      criticalQuadraticLeftLeg b k (oddCapacity_pos hodd) q *
        criticalQuadraticRightLeg b k (oddCapacity_pos hodd) q =
          realizeCountingShare (canonicalResidualDepthMass b k (oddCapacity_pos hodd)) ∧
      criticalQuadraticBracket b k (oddCapacity_pos hodd) q =
        realCenteredReadout (criticalQuadraticLeftLeg b k (oddCapacity_pos hodd) q)
          (realCriticalAmplitude b k (oddCapacity_pos hodd))
          (criticalQuadraticRightLeg b k (oddCapacity_pos hodd) q) := by
  have hprovenance := balancedCarry_depth_and_mass_at_same_index b n k hodd hdepth
  exact ⟨hprovenance.1, hprovenance.2.1, hprovenance.2.2,
    criticalQuadraticLegs_product_realizes_formalMass b k (oddCapacity_pos hodd) q hq, rfl⟩

end

end GeometryOfNumbers.Analysis
