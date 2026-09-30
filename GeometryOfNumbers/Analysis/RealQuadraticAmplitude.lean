import GeometryOfNumbers.Analysis.RealDepthMass

/-!
# Zone B: realizing the selected half-exponent

The foundation already classifies the compatible formal ratios. Here division
and real powers realize those ratios. The critical amplitude uses the formal
presentation `(1,2)`; its square reproducing mass is a realization theorem,
not a new selection argument. No vector state, inner product or norm is built.
-/

namespace GeometryOfNumbers.Analysis

open Foundation

noncomputable section

/-- Interpret a formal ratio numerically; validity is required when using it. -/
def realizeFormalExponent (p q : ℕ) : ℝ := (p : ℝ) / (q : ℝ)

theorem formalHalf_realizes_half {p q : ℕ} (hhalf : FormalExponentRepresentsHalf p q) :
    realizeFormalExponent p q = (1 : ℝ) / 2 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hhalf.1
  have heq : (2 : ℝ) * (p : ℝ) = (q : ℝ) := by exact_mod_cast hhalf.2
  unfold realizeFormalExponent
  apply (div_eq_iff hq).2
  linarith

/-- A real realization of a valid formal exponent, with positive capacity. -/
def realAmplitudeOfFormalExponent (b k p q : ℕ) (_hb : 0 < b) (_hq : 0 < q) : ℝ :=
  (b : ℝ) ^ (-(k : ℝ) * realizeFormalExponent p q)

/-- Realize the selected presentation of half, not a premise of its selection. -/
def realCriticalAmplitude (b k : ℕ) (hb : 0 < b) : ℝ :=
  realAmplitudeOfFormalExponent b k 1 2 hb (by decide)

theorem realCriticalAmplitude_eq_rpow (b k : ℕ) (hb : 0 < b) :
    realCriticalAmplitude b k hb = (b : ℝ) ^ (-(k : ℝ) / 2) := by
  unfold realCriticalAmplitude realAmplitudeOfFormalExponent realizeFormalExponent
  congr 1
  norm_num
  ring

/-- Every formal presentation of half gives the same critical amplitude. -/
theorem formalHalf_realizes_realCriticalAmplitude (b k p q : ℕ) (hb : 0 < b)
    (hhalf : FormalExponentRepresentsHalf p q) :
    realAmplitudeOfFormalExponent b k p q hb hhalf.1 = realCriticalAmplitude b k hb := by
  rw [realCriticalAmplitude_eq_rpow]
  unfold realAmplitudeOfFormalExponent
  rw [formalHalf_realizes_half hhalf]
  congr 1
  ring

/-- Only use the already selected real exponent to verify the square law. -/
theorem realCriticalAmplitude_sq_eq_realDepthMass (b k : ℕ) (hb : 0 < b) :
    realCriticalAmplitude b k hb ^ 2 = realDepthMass b k hb := by
  rw [realCriticalAmplitude_eq_rpow,
    ← Real.rpow_mul_natCast (Nat.cast_nonneg b)]
  norm_num only [Nat.cast_ofNat]
  have heq : (-(k : ℝ) / 2) * (2 : ℝ) = -(k : ℝ) := by ring
  rw [heq]
  exact (realize_canonicalResidualDepthMass b k hb).symm

theorem realCriticalAmplitude_zero (b : ℕ) (hb : 0 < b) :
    realCriticalAmplitude b 0 hb = 1 := by
  rw [realCriticalAmplitude_eq_rpow]
  simp

theorem realCriticalAmplitude_one (k : ℕ) :
    realCriticalAmplitude 1 k Nat.zero_lt_one = 1 := by
  rw [realCriticalAmplitude_eq_rpow]
  simp

/-- Foundation selects the ratio; analysis realizes it. No converse selection proof. -/
theorem quadraticScaleCompatible_realizes_realCriticalAmplitude
    (b k p q : ℕ) (hb : 1 < b) (hk : 0 < k)
    (hcompat : QuadraticAmplitudeScaleCompatibleAt b k p q
      (Nat.lt_trans Nat.zero_lt_one hb)) :
    realAmplitudeOfFormalExponent b k p q (Nat.lt_trans Nat.zero_lt_one hb) hcompat.1 =
      realCriticalAmplitude b k (Nat.lt_trans Nat.zero_lt_one hb) := by
  exact formalHalf_realizes_realCriticalAmplitude b k p q _
    ((canonicalResidualDepthMass_quadraticCompatibility_iff_half b k p q hb hk).1 hcompat)

end

end GeometryOfNumbers.Analysis
