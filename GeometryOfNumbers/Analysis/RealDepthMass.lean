import GeometryOfNumbers.Foundation.FoundationalHalfScalingCapstone
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Zone B: realizing an already derived formal mass

The input is a positive-denominator formal counting share. Division in the
reals interprets that presentation. In particular `realDepthMass` realizes
the EXISTING `canonicalResidualDepthMass`; negative real powers are a theorem
about this realization, not its definition or a premise of the foundation.
This finite-depth mass is not a measure on an infinite tower.
-/

namespace GeometryOfNumbers.Analysis

open Foundation

noncomputable section

/-- Numerical interpretation of a formal presentation with positive denominator. -/
def realizeCountingShare (share : FormalCountingShare) : ℝ :=
  (share.numerator : ℝ) / (share.denominator : ℝ)

/-- The interpretation respects exactly the existing comparison of formal shares. -/
theorem realizeCountingShare_eq_iff_sameCountingShare (left right : FormalCountingShare) :
    realizeCountingShare left = realizeCountingShare right ↔ SameCountingShare left right := by
  have hl : (left.denominator : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt left.denominator_positive
  have hr : (right.denominator : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt right.denominator_positive
  unfold realizeCountingShare SameCountingShare
  rw [div_eq_div_iff hl hr]
  exact_mod_cast (Iff.rfl :
    left.numerator * right.denominator = right.numerator * left.denominator ↔
      left.numerator * right.denominator = right.numerator * left.denominator)

/-- Realize the actual mass produced by prefix counting and geometric refinement. -/
def realDepthMass (b k : ℕ) (hb : 0 < b) : ℝ :=
  realizeCountingShare (canonicalResidualDepthMass b k hb)

theorem realDepthMass_eq_one_div_pow (b k : ℕ) (hb : 0 < b) :
    realDepthMass b k hb = 1 / (b : ℝ) ^ k := by
  unfold realDepthMass
  rw [canonicalResidualDepthMass_eq_radixShare]
  simp [realizeCountingShare, radixShare]

theorem realDepthMass_eq_inv_pow (b k : ℕ) (hb : 0 < b) :
    realDepthMass b k hb = ((b : ℝ) ^ k)⁻¹ := by
  rw [realDepthMass_eq_one_div_pow, one_div]

/-- Negative real powers express the mass already interpreted from formal data. -/
theorem realize_canonicalResidualDepthMass (b k : ℕ) (hb : 0 < b) :
    realizeCountingShare (canonicalResidualDepthMass b k hb) = (b : ℝ) ^ (-(k : ℝ)) := by
  change realDepthMass b k hb = _
  rw [realDepthMass_eq_inv_pow, Real.rpow_neg (Nat.cast_nonneg b), Real.rpow_natCast]

theorem realDepthMass_zero (b : ℕ) (hb : 0 < b) : realDepthMass b 0 hb = 1 := by
  rw [realDepthMass_eq_one_div_pow]
  simp

theorem realDepthMass_one (k : ℕ) : realDepthMass 1 k Nat.zero_lt_one = 1 := by
  rw [realDepthMass_eq_one_div_pow]
  simp

theorem realDepthMass_pos (b k : ℕ) (hb : 0 < b) : 0 < realDepthMass b k hb := by
  rw [realDepthMass_eq_one_div_pow]
  exact one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr hb) k)

end

end GeometryOfNumbers.Analysis
