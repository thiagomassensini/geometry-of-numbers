import SigmaC5RationalNodePreciseLogBounds
import SigmaC5RoundedComplexExp
import SigmaC5RationalNodeInstantiate
import SigmaC5RoundedRationalScale

namespace CarrySigmaObstruction

open ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem c5_two_pow_ge_one (p : ℕ) : (1 : ℚ) ≤ 2 ^ p := by
  induction p with
  | zero => norm_num
  | succ p ih =>
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right ih
        (by norm_num : (0 : ℚ) ≤ (2 : ℚ))]

/-- Outward dyadic rounding grows either endpoint magnitude by at most one. -/
theorem c5CoarsenIntervalAbsBound (p : ℕ) (L : Interval)
    (hLo : |L.lo| ≤ 16) (hHi : |L.hi| ≤ 16) :
    |(L.coarsen p).lo| ≤ 17 ∧ |(L.coarsen p).hi| ≤ 17 := by
  let D : ℚ := 2 ^ p
  have hDpos : 0 < D := by positivity
  have hDge : 1 ≤ D := by simpa [D] using c5_two_pow_ge_one p
  have hfloorLo : L.lo * D - 1 < (Int.floor (L.lo * D) : ℚ) := by
    have h := Int.lt_floor_add_one (L.lo * D)
    linarith
  have hfloorHi : (Int.floor (L.lo * D) : ℚ) ≤ L.lo * D := Int.floor_le _
  have hceilLo : L.hi * D ≤ (Int.ceil (L.hi * D) : ℚ) := Int.le_ceil _
  have hceilHi : (Int.ceil (L.hi * D) : ℚ) < L.hi * D + 1 := by
    have h := Int.ceil_lt_add_one (L.hi * D)
    linarith
  have hLoLower : -16 ≤ L.lo := (abs_le.mp hLo).1
  have hLoUpper : L.lo ≤ 16 := (abs_le.mp hLo).2
  have hHiLower : -16 ≤ L.hi := (abs_le.mp hHi).1
  have hHiUpper : L.hi ≤ 16 := (abs_le.mp hHi).2
  constructor
  · apply abs_le.mpr
    constructor
    · change -17 ≤ (Int.floor (L.lo * D) : ℚ) / D
      rw [le_div_iff₀ hDpos]
      nlinarith
    · change (Int.floor (L.lo * D) : ℚ) / D ≤ 17
      rw [div_le_iff₀ hDpos]
      nlinarith
  · apply abs_le.mpr
    constructor
    · change -17 ≤ (Int.ceil (L.hi * D) : ℚ) / D
      rw [le_div_iff₀ hDpos]
      nlinarith
    · change (Int.ceil (L.hi * D) : ℚ) / D ≤ 17
      rw [div_le_iff₀ hDpos]
      nlinarith

theorem c5CenteredLogQCoarsenedAbsBound (nLog p m : ℕ)
    (hm0 : 1 ≤ m) (hm100 : m ≤ 100) :
    |((c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p).lo| ≤ 17 ∧
      |((c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p).hi| ≤ 17 := by
  exact c5CoarsenIntervalAbsBound p _
    (c5CenteredLogQLogBound nLog m hm0 hm100).1
    (c5CenteredLogQLogBound nLog m hm0 hm100).2

def c5CenteredDirichletTermBoxWithLogTwo (nLog nExp p kE : ℕ)
    (logTwo : Interval) (m : ℕ) (S : ComplexInterval) : ComplexInterval :=
  c5RoundedExpC nExp p kE (S.neg.mul
    { re := (c5CenteredLogQFromLogTwo nLog (c5CenteredLogScale m)
        (m : ℚ) logTwo).coarsen p,
      im := Interval.exact 0 })

theorem c5CenteredDirichletExponentArg_one (nLog p : ℕ)
    (logTwo : Interval) (S : ComplexInterval) :
    S.neg.mul
      { re := (c5CenteredLogQFromLogTwo nLog (c5CenteredLogScale 1)
          (1 : ℚ) logTwo).coarsen p,
        im := Interval.exact 0 } = ComplexInterval.exact 0 0 := by
  rw [c5CenteredLogQFromLogTwo_one]
  simp [ComplexInterval.exact, ComplexInterval.neg, ComplexInterval.mul,
    Interval.exact, Interval.coarsen, Interval.mul, Interval.add,
    Interval.sub, Interval.neg]

theorem c5CenteredDirichletTermBoxWithLogTwo_one
    (nLog nExp p kE : ℕ) (logTwo : Interval) (S : ComplexInterval) :
    c5CenteredDirichletTermBoxWithLogTwo nLog nExp p kE logTwo 1 S =
      c5RoundedExpC nExp p kE (ComplexInterval.exact 0 0) := by
  simp [c5CenteredDirichletTermBoxWithLogTwo,
    c5CenteredDirichletExponentArg_one]

def c5CenteredDirichletTermBox (nLog nExp p kE : ℕ) (m : ℕ)
    (S : ComplexInterval) : ComplexInterval :=
  c5CenteredDirichletTermBoxWithLogTwo nLog nExp p kE
    (c5CenteredLog2I nLog) m S

theorem c5CenteredDirichletTermBoxNormBound {nLog p m : ℕ} {a b : ℚ}
    (hm0 : 1 ≤ m) (hm100 : m ≤ 100)
    (haLo : 2 / 5 ≤ a) (haHi : a ≤ 3 / 5)
    (hbLo : 0 ≤ b) (hbHi : b ≤ 128 / 100000) :
    normBound ((ComplexInterval.exact a b).neg.mul
      { re := (c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p,
        im := Interval.exact 0 }) ≤ 16 := by
  have hL := c5CenteredLogQCoarsenedAbsBound nLog p m hm0 hm100
  have hreal := c5AbsIntervalMulExactEndpoints (c := -a) (M := 17) hL.1 hL.2
  have himag := c5AbsIntervalMulExactEndpoints (c := -b) (M := 17) hL.1 hL.2
  have hbox :
      (ComplexInterval.exact a b).neg.mul
        { re := (c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p,
          im := Interval.exact 0 } =
        { re := (Interval.exact (-a)).mul
            ((c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p),
          im := (Interval.exact (-b)).mul
            ((c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p) } := by
    apply congrArg₂ ComplexInterval.mk
    · simp [ComplexInterval.neg, ComplexInterval.exact, Interval.exact,
        Interval.neg, Interval.mul, Interval.sub, Interval.add]
    · simp [ComplexInterval.neg, ComplexInterval.exact,
        Interval.exact, Interval.neg, Interval.mul, Interval.add]
  rw [hbox]
  change max
      |((Interval.exact (-a)).mul
          ((c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p)).lo|
      |((Interval.exact (-a)).mul
          ((c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p)).hi| +
    max
      |((Interval.exact (-b)).mul
          ((c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p)).lo|
      |((Interval.exact (-b)).mul
          ((c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p)).hi| ≤ 16
  calc
    _ ≤ |a| * 17 + |b| * 17 := by
      simpa only [abs_neg] using
        add_le_add (max_le hreal.1 hreal.2) (max_le himag.1 himag.2)
    _ ≤ (3 / 5 : ℚ) * 17 + (128 / 100000 : ℚ) * 17 := by
      have haAbs : |a| ≤ (3 / 5 : ℚ) := abs_le.mpr ⟨by linarith, by linarith⟩
      have hbAbs : |b| ≤ (128 / 100000 : ℚ) := abs_le.mpr ⟨by linarith, by linarith⟩
      exact add_le_add
        (mul_le_mul_of_nonneg_right haAbs (by norm_num))
        (mul_le_mul_of_nonneg_right hbAbs (by norm_num))
    _ ≤ 16 := by norm_num

theorem c5CenteredDirichletTermBoxContains {nLog nExp p : ℕ}
    (_hnLog : 0 < nLog) (hnExp : 0 < nExp) {m : ℕ} (hm : 0 < m)
    {a b : ℚ} (hm100 : m ≤ 100)
    (haLo : 2 / 5 ≤ a) (haHi : a ≤ 3 / 5)
    (hbLo : 0 ≤ b) (hbHi : b ≤ 128 / 100000) :
    (c5CenteredDirichletTermBox nLog nExp p 4 m
      (ComplexInterval.exact a b)).contains
      ((m : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I))) := by
  have hm0 : 1 ≤ m := by omega
  have hscale := c5CenteredLogScaleRange m hm0 hm100
  have h0 : 0 < (m : ℚ) / 2 ^ c5CenteredLogScale m :=
    lt_of_lt_of_le (by norm_num) hscale.1
  have h2 : (m : ℚ) / 2 ^ c5CenteredLogScale m < 2 :=
    lt_of_le_of_lt hscale.2 (by norm_num)
  have hlog := contains_c5CenteredLogQ (nLog := nLog)
    (k := c5CenteredLogScale m) (q := (m : ℚ)) h0 h2
  have hlog' := Interval.contains_coarsen p hlog
  rw [show (((m : ℚ) : ℝ)) = ((m : ℕ) : ℝ) by push_cast; rfl] at hlog'
  let L : Interval := (c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).coarsen p
  have hL : ({ re := L, im := Interval.exact 0 } : ComplexInterval).contains
      ((Real.log m : ℝ) : ℂ) := by
    constructor
    · change Interval.contains L (Real.log m)
      simpa [L] using hlog'
    · rw [Complex.ofReal_im]
      norm_num [Interval.contains, Interval.exact]
  have hbnd : normBound ((ComplexInterval.exact a b).neg.mul
      { re := L, im := Interval.exact 0 }) ≤ 2 ^ 4 := by
    calc
      _ ≤ 16 := c5CenteredDirichletTermBoxNormBound
        (nLog := nLog) (p := p) (m := m) hm0 hm100 haLo haHi hbLo hbHi
      _ = 2 ^ 4 := by norm_num
  have hs : (ComplexInterval.exact a b).contains
      ((a : ℂ) + (b : ℂ) * Complex.I) := c5ExactRatPoint_contains a b
  have hexp := contains_c5RoundedExpC nExp p hnExp 4 _ _
    (contains_mul (contains_neg hs) hL) hbnd
  have hmne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [show (m : ℂ) ^ (-((a : ℂ) + (b : ℂ) * Complex.I)) =
      Complex.exp (-((a : ℂ) + (b : ℂ) * Complex.I) *
        ((Real.log m : ℝ) : ℂ)) by
    rw [Complex.cpow_def_of_ne_zero hmne,
      show Complex.log (m : ℂ) = ((Real.log m : ℝ) : ℂ) by
        rw [show (m : ℂ) = (((m : ℕ) : ℝ) : ℂ) by push_cast; rfl,
          Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (m : ℝ))],
      mul_comm]]
  simpa [c5CenteredDirichletTermBox, c5CenteredDirichletTermBoxWithLogTwo,
    c5CenteredLogQFromLogTwo, c5CenteredLogQ, L] using hexp

#print axioms c5CenteredLogQCoarsenedAbsBound
#print axioms c5CenteredDirichletTermBoxNormBound
#print axioms c5CenteredDirichletTermBoxContains

end CarrySigmaObstruction
