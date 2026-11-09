import ZetaLean.IntervalCExp
import Mathlib.Tactic

/-!
# Sound complex division for the contour interval evaluator

The contour formula contains `1/s`, `1/(s-1)`, and `ζ'/ζ`.  This module adds a
small verified division operation to the rational rectangle intervals already
used by the C2 and C5 evaluators.  The squared-norm interval is an explicit
input to the quotient theorem; callers must prove that it contains the exact
denominator norm square and that its lower endpoint is positive.

This proves only arithmetic transport.  It does not provide any zeta, digamma,
or arc evaluator enclosures.
-/

namespace ZetaLean

namespace Interval

/-- Tight rational interval enclosure of the square of every real in `x`. -/
def squareRange (x : Interval) : Interval :=
  { lo := if 0 ≤ x.lo then x.lo ^ 2 else if x.hi ≤ 0 then x.hi ^ 2 else 0,
    hi := max (x.lo ^ 2) (x.hi ^ 2),
    le := by
      by_cases hlo : 0 ≤ x.lo
      · simp only [if_pos hlo]
        exact le_max_left _ _
      · by_cases hhi : x.hi ≤ 0
        · simp only [if_neg hlo, if_pos hhi]
          exact le_max_right _ _
        · simp only [if_neg hlo, if_neg hhi]
          exact le_trans (sq_nonneg x.lo) (le_max_left _ _) }

theorem contains_squareRange {x : Interval} {r : ℝ} (hx : x.contains r) :
    (squareRange x).contains (r ^ 2) := by
  rcases hx with ⟨hlo, hhi⟩
  by_cases hloQ : 0 ≤ x.lo
  · have hloR : (0 : ℝ) ≤ (x.lo : ℝ) := by exact_mod_cast hloQ
    have hr0 : 0 ≤ r := le_trans hloR hlo
    have hhiR : (0 : ℝ) ≤ (x.hi : ℝ) := le_trans hloR (by exact_mod_cast x.le)
    have hupper : r ^ 2 ≤ (x.hi : ℝ) ^ 2 := (sq_le_sq₀ hr0 hhiR).2 hhi
    have hlower : (x.lo : ℝ) ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hloR hr0).2 hlo
    constructor
    · simpa [squareRange, hloQ] using hlower
    · simpa [squareRange] using le_trans hupper (le_max_right _ _)
  · by_cases hhiQ : x.hi ≤ 0
    · have hhiR : (x.hi : ℝ) ≤ 0 := by exact_mod_cast hhiQ
      have hr0 : r ≤ 0 := le_trans hhi hhiR
      have hloR : (x.lo : ℝ) ≤ 0 := le_trans hlo hr0
      have hlower : (x.hi : ℝ) ^ 2 ≤ r ^ 2 := by
        have h := (sq_le_sq₀ (show (0 : ℝ) ≤ - (x.hi : ℝ) by linarith)
          (show (0 : ℝ) ≤ -r by linarith)).2
          (show - (x.hi : ℝ) ≤ -r by linarith)
        simpa using h
      have hupper : r ^ 2 ≤ (x.lo : ℝ) ^ 2 := by
        have h := (sq_le_sq₀ (show (0 : ℝ) ≤ -r by linarith)
          (show (0 : ℝ) ≤ - (x.lo : ℝ) by linarith)).2
          (show -r ≤ - (x.lo : ℝ) by linarith)
        simpa using h
      constructor
      · simpa [squareRange, hloQ, hhiQ] using hlower
      · simpa [squareRange, hloQ, hhiQ] using
          le_trans hupper (le_max_left _ _)
    · have hloR : (x.lo : ℝ) < 0 := by
        have h : x.lo < 0 := lt_of_not_ge hloQ
        exact_mod_cast h
      have hhiR : 0 < (x.hi : ℝ) := by
        have h : 0 < x.hi := lt_of_not_ge hhiQ
        exact_mod_cast h
      have hlower : 0 ≤ r ^ 2 := sq_nonneg r
      have hupper : r ^ 2 ≤ max ((x.lo : ℝ) ^ 2) ((x.hi : ℝ) ^ 2) := by
        by_cases hr : 0 ≤ r
        · exact le_trans ((sq_le_sq₀ hr (le_of_lt hhiR)).2 hhi) (le_max_right _ _)
        · have hr' : r ≤ 0 := le_of_not_ge hr
          have hsq : r ^ 2 ≤ (x.lo : ℝ) ^ 2 := by
            have h := (sq_le_sq₀ (show (0 : ℝ) ≤ -r by linarith)
              (show (0 : ℝ) ≤ - (x.lo : ℝ) by linarith)).2
              (show -r ≤ - (x.lo : ℝ) by linarith)
            simpa using h
          exact le_trans hsq (le_max_left _ _)
      constructor
      · simpa [squareRange, hloQ, hhiQ] using hlower
      · simpa [squareRange, hloQ, hhiQ] using hupper

/-- Reciprocal of a strictly positive interval. -/
def reciprocalPositive (x : Interval) (hx0 : 0 < x.lo) : Interval :=
  { lo := 1 / x.hi,
    hi := 1 / x.lo,
    le := one_div_le_one_div_of_le hx0 x.le }

theorem contains_reciprocalPositive {x : Interval} {r : ℝ}
    (hx : x.contains r) (hx0 : 0 < x.lo) :
    (reciprocalPositive x hx0).contains (1 / r) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by exact_mod_cast hx0) hx.1
  constructor
  · have h := one_div_le_one_div_of_le hr0 hx.2
    simpa [reciprocalPositive, Rat.cast_div] using h
  · have h := one_div_le_one_div_of_le (by exact_mod_cast hx0) hx.1
    simpa [reciprocalPositive, Rat.cast_div] using h

end Interval

namespace ComplexInterval

/-- Rational interval enclosure of `x.re² + x.im²`. -/
def normSqRange (x : ComplexInterval) : Interval :=
  (Interval.squareRange x.re).add (Interval.squareRange x.im)

theorem contains_normSqRange {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) : (normSqRange x).contains (Complex.normSq z) := by
  have hre := Interval.contains_squareRange hx.1
  have him := Interval.contains_squareRange hx.2
  have h := Interval.contains_add hre him
  simpa [normSqRange, Complex.normSq, pow_two] using h

/-- Divide the componentwise complex product enclosure by a positive real
interval enclosing the denominator's squared norm. -/
def divBox (num den : ComplexInterval) (denNormSq : Interval)
    (hnormPos : 0 < denNormSq.lo) : ComplexInterval :=
  let recip := Interval.reciprocalPositive denNormSq hnormPos
  { re := ((num.re.mul den.re).add (num.im.mul den.im)).mul recip,
    im := ((num.im.mul den.re).sub (num.re.mul den.im)).mul recip }

/-- Soundness of complex rectangular division. The lower bound on the norm
square proves that the exact denominator is nonzero. -/
theorem contains_divBox {num den : ComplexInterval} {denNormSq : Interval}
    {z w : ℂ}
    (hz : num.contains z) (hw : den.contains w)
    (hnorm : denNormSq.contains (Complex.normSq w))
    (hnormPos : 0 < denNormSq.lo) :
    (divBox num den denNormSq hnormPos).contains (z / w) := by
  have hrecip := Interval.contains_reciprocalPositive hnorm hnormPos
  have hnumRe : ((num.re.mul den.re).add (num.im.mul den.im)).contains
      (z.re * w.re + z.im * w.im) :=
    Interval.contains_add (Interval.contains_mul hz.1 hw.1)
      (Interval.contains_mul hz.2 hw.2)
  have hnumIm : ((num.im.mul den.re).sub (num.re.mul den.im)).contains
      (z.im * w.re - z.re * w.im) :=
    Interval.contains_sub (Interval.contains_mul hz.2 hw.1)
      (Interval.contains_mul hz.1 hw.2)
  have hreal := Interval.contains_mul hnumRe hrecip
  have himag := Interval.contains_mul hnumIm hrecip
  have hwNorm : Complex.normSq w ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by exact_mod_cast hnormPos) hnorm.1)
  constructor
  · have hformula :
        (z.re * w.re + z.im * w.im) * (1 / Complex.normSq w) = (z / w).re := by
      rw [Complex.div_re]
      field_simp [hwNorm]
    rw [hformula] at hreal
    simpa [divBox] using hreal
  · have hformula :
        (z.im * w.re - z.re * w.im) * (1 / Complex.normSq w) = (z / w).im := by
      rw [Complex.div_im]
      field_simp [hwNorm]
    rw [hformula] at himag
    simpa [divBox] using himag

end ComplexInterval
end ZetaLean

namespace CarrySigmaObstruction

open ZetaLean

#print axioms Interval.contains_squareRange
#print axioms Interval.contains_reciprocalPositive
#print axioms ComplexInterval.contains_normSqRange
#print axioms ComplexInterval.contains_divBox

end CarrySigmaObstruction
