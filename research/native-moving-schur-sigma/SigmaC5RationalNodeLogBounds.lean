import SigmaC5RationalNodeEval

namespace CarrySigmaObstruction

open ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Choose the binary reduction separately for each Dirichlet index, keeping
the reduced argument in `[1/2,1]` and the logarithm series ratio in `[0,1/2]`.
This avoids the slow `q≈1` endpoint of a single fixed reduction for `m=1`. -/
def c5AdaptiveLogScale (m : ℕ) : ℕ :=
  if m ≤ 1 then 0 else if m ≤ 2 then 1 else if m ≤ 4 then 2 else
  if m ≤ 8 then 3 else if m ≤ 16 then 4 else if m ≤ 32 then 5 else
  if m ≤ 64 then 6 else 7

/-- Kernel-reduced rational endpoints of the adaptive `logQ` boxes stay in
`[-5,5]` for all Dirichlet indices used by the 100-term Euler--Maclaurin head. -/
theorem c5LogQAdaptiveAbsBound (m : ℕ) (hm0 : 1 ≤ m) (hm100 : m ≤ 100) :
    |(Interval.logQ 128 (c5AdaptiveLogScale m) (m : ℚ)).lo| ≤ 5 ∧
      |(Interval.logQ 128 (c5AdaptiveLogScale m) (m : ℚ)).hi| ≤ 5 := by
  interval_cases m <;>
    norm_num [c5AdaptiveLogScale, Interval.logQ, Interval.log2I, Interval.log1,
      Interval.logSum, Interval.logRem, Interval.exact, Interval.neg,
      Interval.add, Interval.mul]

theorem c5AdaptiveLogScaleValid (m : ℕ) (hm0 : 1 ≤ m) (hm100 : m ≤ 100) :
    0 < (m : ℚ) / 2 ^ c5AdaptiveLogScale m ∧
      (m : ℚ) / 2 ^ c5AdaptiveLogScale m < 2 := by
  interval_cases m <;> norm_num [c5AdaptiveLogScale]

theorem c5AbsMinLe {x y M : ℚ} (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |min x y| ≤ M := by
  apply abs_le.mpr
  constructor
  · exact le_min (abs_le.mp hx).1 (abs_le.mp hy).1
  · exact (min_le_left x y).trans (abs_le.mp hx).2

theorem c5AbsMaxLe {x y M : ℚ} (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |max x y| ≤ M := by
  apply abs_le.mpr
  constructor
  · exact (abs_le.mp hx).1.trans (le_max_left x y)
  · exact max_le (abs_le.mp hx).2 (abs_le.mp hy).2

theorem c5AbsIntervalMulExactEndpoints {c M : ℚ} {L : Interval}
    (hlo : |L.lo| ≤ M) (hhi : |L.hi| ≤ M) :
    |((Interval.exact c).mul L).lo| ≤ |c| * M ∧
      |((Interval.exact c).mul L).hi| ≤ |c| * M := by
  have hcLo : |c * L.lo| ≤ |c| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hlo (abs_nonneg c)
  have hcHi : |c * L.hi| ≤ |c| * M := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hhi (abs_nonneg c)
  constructor
  · change |min (min (c * L.lo) (c * L.hi))
      (min (c * L.lo) (c * L.hi))| ≤ |c| * M
    exact c5AbsMinLe (c5AbsMinLe hcLo hcHi) (c5AbsMinLe hcLo hcHi)
  · change |max (max (c * L.lo) (c * L.hi))
      (max (c * L.lo) (c * L.hi))| ≤ |c| * M
    exact c5AbsMaxLe (c5AbsMaxLe hcLo hcHi) (c5AbsMaxLe hcLo hcHi)

theorem c5AdaptiveProductNormBoundLeFour {a b : ℚ} {L : Interval}
    (haLo : 2 / 5 ≤ a) (haHi : a ≤ 3 / 5)
    (hbLo : 0 ≤ b) (hbHi : b ≤ 128 / 100000)
    (hLLo : |L.lo| ≤ 5) (hLHi : |L.hi| ≤ 5) :
    ComplexInterval.normBound
      ((ComplexInterval.exact a b).neg.mul { re := L, im := Interval.exact 0 }) ≤ 4 := by
  have hreal := c5AbsIntervalMulExactEndpoints (c := -a) (M := 5) hLLo hLHi
  have himag := c5AbsIntervalMulExactEndpoints (c := -b) (M := 5) hLLo hLHi
  have hbox :
      (ComplexInterval.exact a b).neg.mul { re := L, im := Interval.exact 0 } =
        { re := (Interval.exact (-a)).mul L,
          im := (Interval.exact (-b)).mul L } := by
    apply congrArg₂ ComplexInterval.mk
    · simp [ComplexInterval.neg, ComplexInterval.exact, Interval.exact,
        Interval.neg, Interval.mul, Interval.sub, Interval.add]
    · simp [ComplexInterval.neg, ComplexInterval.exact,
        Interval.exact, Interval.neg, Interval.mul, Interval.add]
  rw [hbox]
  change max |((Interval.exact (-a)).mul L).lo| |((Interval.exact (-a)).mul L).hi| +
    max |((Interval.exact (-b)).mul L).lo| |((Interval.exact (-b)).mul L).hi| ≤ 4
  calc
    _ ≤ |a| * 5 + |b| * 5 := by
      simpa only [abs_neg] using
        add_le_add (max_le hreal.1 hreal.2) (max_le himag.1 himag.2)
    _ ≤ (3 / 5 : ℚ) * 5 + (128 / 100000 : ℚ) * 5 := by
      have haAbs : |a| ≤ (3 / 5 : ℚ) := abs_le.mpr ⟨by linarith, by linarith⟩
      have hbAbs : |b| ≤ (128 / 100000 : ℚ) := abs_le.mpr ⟨by linarith, by linarith⟩
      exact add_le_add (mul_le_mul_of_nonneg_right haAbs (by norm_num))
        (mul_le_mul_of_nonneg_right hbAbs (by norm_num))
    _ ≤ 4 := by norm_num

end CarrySigmaObstruction
