import SigmaC5GammaComplexNodeDOneUpperComplexCombine
import SigmaC5GammaDOneUpperLogBounds
import Mathlib.Tactic

namespace CarrySigmaObstruction

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Complex Gamma node for displacement `d = 1/10`: argument `3/10 + 3i/20`. -/
noncomputable def c5GammaComplexNodeDOneUpperComplexPoint : ℂ :=
  (3 / 10 : ℂ) + (3 / 20 : ℂ) * Complex.I

def c5GammaComplexNodeDOneUpperComplexPowerBox : ComplexInterval :=
  ComplexInterval.dirichletTermBox2 384 64 320 8 3 240
    (gammaFiniteNegativePointBox (3 / 10) (3 / 20))

def c5GammaComplexNodeDOneUpperComplexFiniteBox : ComplexInterval :=
  c5GammaComplexNodeDOneUpperComplexPowerBox.mul c5GammaComplexNodeDOneUpperComplexCoreBox

def c5GammaComplexNodeDOneUpperComplexBox : ComplexInterval :=
  c5GammaComplexNodeDOneUpperComplexFiniteBox.inflate (1 / 10 ^ 99)

theorem c5GammaComplexNodeDOneUpperComplexPowerArg_normBound :
    ComplexInterval.normBound
      ((gammaFiniteNegativePointBox (3 / 10) (3 / 20)).neg.mul
        { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 8 := by
  have hlog := c5GammaDOneUpper_logQ_absBound
  have hre := c5AbsIntervalMulExactEndpoints
    (c := (3 / 10 : ℚ)) (M := 10) hlog.1 hlog.2
  have him := c5AbsIntervalMulExactEndpoints
    (c := (3 / 20 : ℚ)) (M := 10) hlog.1 hlog.2
  unfold gammaFiniteNegativePointBox
  simp only [ComplexInterval.neg, ComplexInterval.exact, Interval.neg,
    Interval.exact, neg_neg]
  change ComplexInterval.normBound
    ((ComplexInterval.exact (3 / 10 : ℚ) (3 / 20 : ℚ)).mul
      { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 8
  rw [ComplexInterval.normBound, ComplexInterval.mul, ComplexInterval.exact]
  have hzeroRe : (Interval.exact (3 / 10 : ℚ)).mul
      (Interval.exact 0) = Interval.exact 0 := by
    simp [Interval.mul, Interval.exact]
  have hzeroIm : (Interval.exact (3 / 20 : ℚ)).mul
      (Interval.exact 0) = Interval.exact 0 := by
    simp [Interval.mul, Interval.exact]
  rw [hzeroIm, hzeroRe]
  simp only [Interval.sub, Interval.add, Interval.neg, Interval.exact,
    neg_zero, add_zero, zero_add]
  calc
    max |((Interval.exact (3 / 10 : ℚ)).mul
        (Interval.logQ 384 8 240)).lo|
        |((Interval.exact (3 / 10 : ℚ)).mul
        (Interval.logQ 384 8 240)).hi| +
      max |((Interval.exact (3 / 20 : ℚ)).mul
        (Interval.logQ 384 8 240)).lo|
        |((Interval.exact (3 / 20 : ℚ)).mul
        (Interval.logQ 384 8 240)).hi| ≤
      |(3 / 10 : ℚ)| * 10 + |(3 / 20 : ℚ)| * 10 := by
        exact add_le_add (max_le hre.1 hre.2) (max_le him.1 him.2)
    _ ≤ 8 := by norm_num

theorem c5GammaComplexNodeDOneUpperComplexPowerBox_contains :
    c5GammaComplexNodeDOneUpperComplexPowerBox.contains
      ((240 : ℂ) ^ c5GammaComplexNodeDOneUpperComplexPoint) := by
  have hS : (gammaFiniteNegativePointBox (3 / 10) (3 / 20)).contains
      (-c5GammaComplexNodeDOneUpperComplexPoint) := by
    change
      Interval.contains (Interval.exact (-(3 / 10 : ℚ)))
          (-c5GammaComplexNodeDOneUpperComplexPoint).re ∧
        Interval.contains (Interval.exact (-(3 / 20 : ℚ)))
          (-c5GammaComplexNodeDOneUpperComplexPoint).im
    constructor
    · simpa [c5GammaComplexNodeDOneUpperComplexPoint] using
        Interval.contains_exact (-(3 / 10 : ℚ))
    · simpa [c5GammaComplexNodeDOneUpperComplexPoint] using
        Interval.contains_exact (-(3 / 20 : ℚ))
  have hb : ComplexInterval.normBound
      ((gammaFiniteNegativePointBox (3 / 10) (3 / 20)).neg.mul
        { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 2 ^ 3 := by
    calc
      _ ≤ 8 := c5GammaComplexNodeDOneUpperComplexPowerArg_normBound
      _ = 2 ^ 3 := by norm_num
  have h := ComplexInterval.contains_dirichletTermBox2
    (nLog := 384) (nExp := 64) (p := 320) (kL := 8) (kE := 3)
    (by norm_num) (by norm_num) (m := 240) (by norm_num)
    (S := gammaFiniteNegativePointBox (3 / 10) (3 / 20))
    (s := -c5GammaComplexNodeDOneUpperComplexPoint) hS (by norm_num) (by norm_num) hb
  simpa [c5GammaComplexNodeDOneUpperComplexPowerBox, c5GammaComplexNodeDOneUpperComplexPoint,
    gammaFiniteNegativePointBox] using h

theorem c5GammaComplexNodeDOneUpperComplexBox_contains :
    c5GammaComplexNodeDOneUpperComplexBox.contains (Complex.Gamma c5GammaComplexNodeDOneUpperComplexPoint) := by
  have hpow := c5GammaComplexNodeDOneUpperComplexPowerBox_contains
  have hfiniteEq :
      gammaFinite 1024 240 c5GammaComplexNodeDOneUpperComplexPoint =
        (240 : ℂ) ^ c5GammaComplexNodeDOneUpperComplexPoint *
          ratComplexToComplex
            (gammaFiniteRationalCore 1024 240 (3 / 10) (3 / 20)) := by
    simpa [c5GammaComplexNodeDOneUpperComplexPoint] using
      (gammaFinite_eq_rationalCore 1024 240 (3 / 10) (3 / 20) (by norm_num))
  have hfinite : c5GammaComplexNodeDOneUpperComplexFiniteBox.contains
      (gammaFinite 1024 240 c5GammaComplexNodeDOneUpperComplexPoint) := by
    rw [hfiniteEq]
    simpa [c5GammaComplexNodeDOneUpperComplexFiniteBox, c5GammaComplexNodeDOneUpperComplexCore] using
      ComplexInterval.contains_mul hpow c5GammaComplexNodeDOneUpperComplexCoreBox_contains
  have herr := gamma_finite_1024_240_error c5GammaComplexNodeDOneUpperComplexPoint
    (by norm_num [c5GammaComplexNodeDOneUpperComplexPoint])
    (by norm_num [c5GammaComplexNodeDOneUpperComplexPoint])
  have herr' :
      ‖Complex.Gamma c5GammaComplexNodeDOneUpperComplexPoint -
        gammaFinite 1024 240 c5GammaComplexNodeDOneUpperComplexPoint‖ ≤
          (((1 : ℚ) / 10 ^ 99 : ℚ) : ℝ) := by
    simpa using herr
  exact ComplexInterval.contains_inflate hfinite herr'

#print axioms c5GammaComplexNodeDOneUpperComplexPowerArg_normBound
#print axioms c5GammaComplexNodeDOneUpperComplexPowerBox_contains
#print axioms c5GammaComplexNodeDOneUpperComplexBox_contains

end CarrySigmaObstruction
