import SigmaC5GammaComplexNodeCombine
import SigmaC5GammaSecondRealPointGammaCertificate
import Mathlib.Tactic

namespace CarrySigmaObstruction

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- First complex Gamma node for `d = 99/2000`, at Cauchy height `3/10`. -/
noncomputable def c5GammaComplexNodePoint : ℂ :=
  (901 / 4000 : ℂ) + (3 / 20 : ℂ) * Complex.I

def c5GammaComplexNodePowerBox : ComplexInterval :=
  ComplexInterval.dirichletTermBox2 384 64 320 8 3 240
    (gammaFiniteNegativePointBox (901 / 4000) (3 / 20))

def c5GammaComplexNodeFiniteBox : ComplexInterval :=
  c5GammaComplexNodePowerBox.mul c5GammaComplexNodeCoreBox

def c5GammaComplexNodeBox : ComplexInterval :=
  c5GammaComplexNodeFiniteBox.inflate (1 / 10 ^ 99)

theorem c5GammaComplexNodePowerArg_normBound :
    ComplexInterval.normBound
      ((gammaFiniteNegativePointBox (901 / 4000) (3 / 20)).neg.mul
        { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 8 := by
  have hlog := c5GammaSecondRealPoint_logQ_absBound
  have hre := c5AbsIntervalMulExactEndpoints
    (c := (901 / 4000 : ℚ)) (M := 18) hlog.1 hlog.2
  have him := c5AbsIntervalMulExactEndpoints
    (c := (3 / 20 : ℚ)) (M := 18) hlog.1 hlog.2
  unfold gammaFiniteNegativePointBox
  simp only [ComplexInterval.neg, ComplexInterval.exact, Interval.neg,
    Interval.exact, neg_neg]
  change ComplexInterval.normBound
    ((ComplexInterval.exact (901 / 4000 : ℚ) (3 / 20 : ℚ)).mul
      { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 8
  rw [ComplexInterval.normBound, ComplexInterval.mul, ComplexInterval.exact]
  have hzeroRe : (Interval.exact (901 / 4000 : ℚ)).mul
      (Interval.exact 0) = Interval.exact 0 := by
    simp [Interval.mul, Interval.exact]
  have hzeroIm : (Interval.exact (3 / 20 : ℚ)).mul
      (Interval.exact 0) = Interval.exact 0 := by
    simp [Interval.mul, Interval.exact]
  rw [hzeroIm, hzeroRe]
  simp only [Interval.sub, Interval.add, Interval.neg, Interval.exact,
    neg_zero, add_zero, zero_add]
  calc
    max |((Interval.exact (901 / 4000 : ℚ)).mul
        (Interval.logQ 384 8 240)).lo|
        |((Interval.exact (901 / 4000 : ℚ)).mul
        (Interval.logQ 384 8 240)).hi| +
      max |((Interval.exact (3 / 20 : ℚ)).mul
        (Interval.logQ 384 8 240)).lo|
        |((Interval.exact (3 / 20 : ℚ)).mul
        (Interval.logQ 384 8 240)).hi| ≤
      |(901 / 4000 : ℚ)| * 18 + |(3 / 20 : ℚ)| * 18 := by
        exact add_le_add (max_le hre.1 hre.2) (max_le him.1 him.2)
    _ ≤ 8 := by norm_num

theorem c5GammaComplexNodePowerBox_contains :
    c5GammaComplexNodePowerBox.contains
      ((240 : ℂ) ^ c5GammaComplexNodePoint) := by
  have hS : (gammaFiniteNegativePointBox (901 / 4000) (3 / 20)).contains
      (-c5GammaComplexNodePoint) := by
    change
      Interval.contains (Interval.exact (-(901 / 4000 : ℚ)))
          (-c5GammaComplexNodePoint).re ∧
        Interval.contains (Interval.exact (-(3 / 20 : ℚ)))
          (-c5GammaComplexNodePoint).im
    constructor
    · simpa [c5GammaComplexNodePoint] using
        Interval.contains_exact (-(901 / 4000 : ℚ))
    · simpa [c5GammaComplexNodePoint] using
        Interval.contains_exact (-(3 / 20 : ℚ))
  have hb : ComplexInterval.normBound
      ((gammaFiniteNegativePointBox (901 / 4000) (3 / 20)).neg.mul
        { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 2 ^ 3 := by
    calc
      _ ≤ 8 := c5GammaComplexNodePowerArg_normBound
      _ = 2 ^ 3 := by norm_num
  have h := ComplexInterval.contains_dirichletTermBox2
    (nLog := 384) (nExp := 64) (p := 320) (kL := 8) (kE := 3)
    (by norm_num) (by norm_num) (m := 240) (by norm_num)
    (S := gammaFiniteNegativePointBox (901 / 4000) (3 / 20))
    (s := -c5GammaComplexNodePoint) hS (by norm_num) (by norm_num) hb
  simpa [c5GammaComplexNodePowerBox, c5GammaComplexNodePoint,
    gammaFiniteNegativePointBox] using h

theorem c5GammaComplexNodeBox_contains :
    c5GammaComplexNodeBox.contains (Complex.Gamma c5GammaComplexNodePoint) := by
  have hpow := c5GammaComplexNodePowerBox_contains
  have hfiniteEq :
      gammaFinite 1024 240 c5GammaComplexNodePoint =
        (240 : ℂ) ^ c5GammaComplexNodePoint *
          ratComplexToComplex
            (gammaFiniteRationalCore 1024 240 (901 / 4000) (3 / 20)) := by
    simpa [c5GammaComplexNodePoint] using
      (gammaFinite_eq_rationalCore 1024 240 (901 / 4000) (3 / 20) (by norm_num))
  have hfinite : c5GammaComplexNodeFiniteBox.contains
      (gammaFinite 1024 240 c5GammaComplexNodePoint) := by
    rw [hfiniteEq]
    simpa [c5GammaComplexNodeFiniteBox, c5GammaComplexNodeCore] using
      ComplexInterval.contains_mul hpow c5GammaComplexNodeCoreBox_contains
  have herr := gamma_finite_1024_240_error c5GammaComplexNodePoint
    (by norm_num [c5GammaComplexNodePoint])
    (by norm_num [c5GammaComplexNodePoint])
  have herr' :
      ‖Complex.Gamma c5GammaComplexNodePoint -
        gammaFinite 1024 240 c5GammaComplexNodePoint‖ ≤
          (((1 : ℚ) / 10 ^ 99 : ℚ) : ℝ) := by
    simpa using herr
  exact ComplexInterval.contains_inflate hfinite herr'

#print axioms c5GammaComplexNodePowerArg_normBound
#print axioms c5GammaComplexNodePowerBox_contains
#print axioms c5GammaComplexNodeBox_contains

end CarrySigmaObstruction
