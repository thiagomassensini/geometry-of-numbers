import SigmaC5GammaComplexNodeDOneComplexCombine
import SigmaC5GammaSecondRealPointGammaCertificate
import Mathlib.Tactic

namespace CarrySigmaObstruction

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Complex Gamma node for displacement `d = 1/10`: argument `1/5 + 3i/20`. -/
noncomputable def c5GammaComplexNodeDOneComplexPoint : ℂ :=
  (1 / 5 : ℂ) + (3 / 20 : ℂ) * Complex.I

def c5GammaComplexNodeDOneComplexPowerBox : ComplexInterval :=
  ComplexInterval.dirichletTermBox2 384 64 320 8 3 240
    (gammaFiniteNegativePointBox (1 / 5) (3 / 20))

def c5GammaComplexNodeDOneComplexFiniteBox : ComplexInterval :=
  c5GammaComplexNodeDOneComplexPowerBox.mul c5GammaComplexNodeDOneComplexCoreBox

def c5GammaComplexNodeDOneComplexBox : ComplexInterval :=
  c5GammaComplexNodeDOneComplexFiniteBox.inflate (1 / 10 ^ 99)

theorem c5GammaComplexNodeDOneComplexPowerArg_normBound :
    ComplexInterval.normBound
      ((gammaFiniteNegativePointBox (1 / 5) (3 / 20)).neg.mul
        { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 8 := by
  have hlog := c5GammaSecondRealPoint_logQ_absBound
  have hre := c5AbsIntervalMulExactEndpoints
    (c := (1 / 5 : ℚ)) (M := 18) hlog.1 hlog.2
  have him := c5AbsIntervalMulExactEndpoints
    (c := (3 / 20 : ℚ)) (M := 18) hlog.1 hlog.2
  unfold gammaFiniteNegativePointBox
  simp only [ComplexInterval.neg, ComplexInterval.exact, Interval.neg,
    Interval.exact, neg_neg]
  change ComplexInterval.normBound
    ((ComplexInterval.exact (1 / 5 : ℚ) (3 / 20 : ℚ)).mul
      { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 8
  rw [ComplexInterval.normBound, ComplexInterval.mul, ComplexInterval.exact]
  have hzeroRe : (Interval.exact (1 / 5 : ℚ)).mul
      (Interval.exact 0) = Interval.exact 0 := by
    simp [Interval.mul, Interval.exact]
  have hzeroIm : (Interval.exact (3 / 20 : ℚ)).mul
      (Interval.exact 0) = Interval.exact 0 := by
    simp [Interval.mul, Interval.exact]
  rw [hzeroIm, hzeroRe]
  simp only [Interval.sub, Interval.add, Interval.neg, Interval.exact,
    neg_zero, add_zero, zero_add]
  calc
    max |((Interval.exact (1 / 5 : ℚ)).mul
        (Interval.logQ 384 8 240)).lo|
        |((Interval.exact (1 / 5 : ℚ)).mul
        (Interval.logQ 384 8 240)).hi| +
      max |((Interval.exact (3 / 20 : ℚ)).mul
        (Interval.logQ 384 8 240)).lo|
        |((Interval.exact (3 / 20 : ℚ)).mul
        (Interval.logQ 384 8 240)).hi| ≤
      |(1 / 5 : ℚ)| * 18 + |(3 / 20 : ℚ)| * 18 := by
        exact add_le_add (max_le hre.1 hre.2) (max_le him.1 him.2)
    _ ≤ 8 := by norm_num

theorem c5GammaComplexNodeDOneComplexPowerBox_contains :
    c5GammaComplexNodeDOneComplexPowerBox.contains
      ((240 : ℂ) ^ c5GammaComplexNodeDOneComplexPoint) := by
  have hS : (gammaFiniteNegativePointBox (1 / 5) (3 / 20)).contains
      (-c5GammaComplexNodeDOneComplexPoint) := by
    change
      Interval.contains (Interval.exact (-(1 / 5 : ℚ)))
          (-c5GammaComplexNodeDOneComplexPoint).re ∧
        Interval.contains (Interval.exact (-(3 / 20 : ℚ)))
          (-c5GammaComplexNodeDOneComplexPoint).im
    constructor
    · simpa [c5GammaComplexNodeDOneComplexPoint] using
        Interval.contains_exact (-(1 / 5 : ℚ))
    · simpa [c5GammaComplexNodeDOneComplexPoint] using
        Interval.contains_exact (-(3 / 20 : ℚ))
  have hb : ComplexInterval.normBound
      ((gammaFiniteNegativePointBox (1 / 5) (3 / 20)).neg.mul
        { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 2 ^ 3 := by
    calc
      _ ≤ 8 := c5GammaComplexNodeDOneComplexPowerArg_normBound
      _ = 2 ^ 3 := by norm_num
  have h := ComplexInterval.contains_dirichletTermBox2
    (nLog := 384) (nExp := 64) (p := 320) (kL := 8) (kE := 3)
    (by norm_num) (by norm_num) (m := 240) (by norm_num)
    (S := gammaFiniteNegativePointBox (1 / 5) (3 / 20))
    (s := -c5GammaComplexNodeDOneComplexPoint) hS (by norm_num) (by norm_num) hb
  simpa [c5GammaComplexNodeDOneComplexPowerBox, c5GammaComplexNodeDOneComplexPoint,
    gammaFiniteNegativePointBox] using h

theorem c5GammaComplexNodeDOneComplexBox_contains :
    c5GammaComplexNodeDOneComplexBox.contains (Complex.Gamma c5GammaComplexNodeDOneComplexPoint) := by
  have hpow := c5GammaComplexNodeDOneComplexPowerBox_contains
  have hfiniteEq :
      gammaFinite 1024 240 c5GammaComplexNodeDOneComplexPoint =
        (240 : ℂ) ^ c5GammaComplexNodeDOneComplexPoint *
          ratComplexToComplex
            (gammaFiniteRationalCore 1024 240 (1 / 5) (3 / 20)) := by
    simpa [c5GammaComplexNodeDOneComplexPoint] using
      (gammaFinite_eq_rationalCore 1024 240 (1 / 5) (3 / 20) (by norm_num))
  have hfinite : c5GammaComplexNodeDOneComplexFiniteBox.contains
      (gammaFinite 1024 240 c5GammaComplexNodeDOneComplexPoint) := by
    rw [hfiniteEq]
    simpa [c5GammaComplexNodeDOneComplexFiniteBox, c5GammaComplexNodeDOneComplexCore] using
      ComplexInterval.contains_mul hpow c5GammaComplexNodeDOneComplexCoreBox_contains
  have herr := gamma_finite_1024_240_error c5GammaComplexNodeDOneComplexPoint
    (by norm_num [c5GammaComplexNodeDOneComplexPoint])
    (by norm_num [c5GammaComplexNodeDOneComplexPoint])
  have herr' :
      ‖Complex.Gamma c5GammaComplexNodeDOneComplexPoint -
        gammaFinite 1024 240 c5GammaComplexNodeDOneComplexPoint‖ ≤
          (((1 : ℚ) / 10 ^ 99 : ℚ) : ℝ) := by
    simpa using herr
  exact ComplexInterval.contains_inflate hfinite herr'

#print axioms c5GammaComplexNodeDOneComplexPowerArg_normBound
#print axioms c5GammaComplexNodeDOneComplexPowerBox_contains
#print axioms c5GammaComplexNodeDOneComplexBox_contains

end CarrySigmaObstruction
