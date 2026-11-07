import SigmaC5GammaCoreChunk64Combine
import SigmaC5RationalNodeLogBounds
import Mathlib.Tactic

namespace CarrySigmaObstruction

open SigmaC5Gamma ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable def c5GammaCoreFirstNodePoint : ℂ := (1 / 5 : ℂ)

private theorem c5GammaFirstNode_geom_half (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 1)) =
      1 - (1 / 2 : ℚ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

private theorem c5GammaFirstNode_abs_logSum_half {n : ℕ} {q : ℚ}
    (hq : |q| ≤ 1 / 2) : |Interval.logSum n q| ≤ 1 := by
  unfold Interval.logSum
  calc
    |∑ i ∈ Finset.range n, q ^ (i + 1) / (i + 1)| ≤
        ∑ i ∈ Finset.range n, |q ^ (i + 1) / (i + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hden : (1 : ℚ) ≤ (i : ℚ) + 1 := by
        exact_mod_cast (show 1 ≤ i + 1 by omega)
      rw [abs_div, abs_pow,
        abs_of_nonneg (by positivity : (0 : ℚ) ≤ (i + 1 : ℚ))]
      calc
        |q| ^ (i + 1) / (i + 1 : ℚ) ≤ |q| ^ (i + 1) :=
          div_le_self (by positivity) hden
        _ ≤ (1 / 2 : ℚ) ^ (i + 1) :=
          pow_le_pow_left₀ (abs_nonneg q) hq (i + 1)
    _ = 1 - (1 / 2 : ℚ) ^ n := c5GammaFirstNode_geom_half n
    _ ≤ 1 := by
      have hn : 0 ≤ (1 / 2 : ℚ) ^ n := pow_nonneg (by norm_num) _
      linarith

private theorem c5GammaFirstNode_abs_logRem_half {n : ℕ} {q : ℚ}
    (hq : |q| ≤ 1 / 2) : |Interval.logRem n q| ≤ 1 := by
  unfold Interval.logRem
  have hden : 0 < 1 - |q| := by linarith [abs_nonneg q]
  have hpow : |q| ^ (n + 1) ≤ (1 / 2 : ℚ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg q) hq (n + 1)
  have hnum : |q| ^ (n + 1) ≤ 1 / 2 := by
    calc
      |q| ^ (n + 1) ≤ (1 / 2 : ℚ) ^ (n + 1) := hpow
      _ ≤ 1 / 2 := by
        have hpow' : (1 / 2 : ℚ) ^ n ≤ 1 :=
          pow_le_one₀ (by norm_num : (0 : ℚ) ≤ 1 / 2)
            (by norm_num : (1 / 2 : ℚ) ≤ 1)
        rw [pow_succ]
        simpa using mul_le_mul_of_nonneg_right hpow'
          (by norm_num : (0 : ℚ) ≤ (1 / 2 : ℚ))
  rw [abs_of_nonneg (div_nonneg (pow_nonneg (abs_nonneg q) _) (le_of_lt hden))]
  rw [div_le_iff₀ hden]
  nlinarith [hq]

private theorem c5GammaFirstNode_abs_max_le {x y M : ℚ}
    (hx : |x| ≤ M) (hy : |y| ≤ M) : |max x y| ≤ M := by
  apply abs_le.mpr
  constructor
  · exact (abs_le.mp hx).1.trans (le_max_left _ _)
  · exact max_le (abs_le.mp hx).2 (abs_le.mp hy).2

private theorem c5GammaFirstNode_log1_half_endpoint_bound (n : ℕ) (x : ℚ)
    (hq : |1 - x| ≤ 1 / 2) :
    |(Interval.log1 n (Interval.exact x)).lo| ≤ 2 ∧
      |(Interval.log1 n (Interval.exact x)).hi| ≤ 2 := by
  have hs := c5GammaFirstNode_abs_logSum_half (n := n) (q := 1 - x) hq
  have hr := c5GammaFirstNode_abs_logRem_half (n := n) (q := 1 - x) hq
  have hlo : |-(Interval.logSum n (1 - x)) - Interval.logRem n (1 - x)| ≤ 2 := by
    calc
      |-(Interval.logSum n (1 - x)) - Interval.logRem n (1 - x)| ≤
          |Interval.logSum n (1 - x)| + |Interval.logRem n (1 - x)| := by
        rw [show -Interval.logSum n (1 - x) - Interval.logRem n (1 - x) =
          -(Interval.logSum n (1 - x) + Interval.logRem n (1 - x)) by ring,
          abs_neg]
        exact abs_add_le _ _
      _ ≤ 2 := by linarith
  have hhi0 : |-Interval.logSum n (1 - x) + Interval.logRem n (1 - x)| ≤ 2 := by
    calc
      |-Interval.logSum n (1 - x) + Interval.logRem n (1 - x)| ≤
          |Interval.logSum n (1 - x)| + |Interval.logRem n (1 - x)| := by
        simpa [abs_neg] using
          (abs_add_le (-Interval.logSum n (1 - x)) (Interval.logRem n (1 - x)))
      _ ≤ 2 := by linarith
  constructor
  · simpa [Interval.log1, Interval.exact] using hlo
  · change |max (-Interval.logSum n (1 - x) + Interval.logRem n (1 - x))
      (-Interval.logSum n (1 - x) - Interval.logRem n (1 - x))| ≤ 2
    exact c5GammaFirstNode_abs_max_le hhi0 hlo

private theorem c5GammaFirstNode_logQ_absBound :
    |(Interval.logQ 384 8 240).lo| ≤ 18 ∧
      |(Interval.logQ 384 8 240).hi| ≤ 18 := by
  have hq : |1 - (240 : ℚ) / 2 ^ 8| ≤ 1 / 2 := by norm_num
  have hlog1 := c5GammaFirstNode_log1_half_endpoint_bound 384
    ((240 : ℚ) / 2 ^ 8) hq
  have hlog1' :
      |(Interval.log1 384 (Interval.exact ((240 : ℚ) / 2 ^ 8))).lo| ≤ 2 ∧
        |(Interval.log1 384 (Interval.exact ((240 : ℚ) / 2 ^ 8))).hi| ≤ 2 := hlog1
  have hlog2base := c5GammaFirstNode_log1_half_endpoint_bound 384
    (1 / 2 : ℚ) (by norm_num)
  have hlog2 : |(Interval.log2I 384).lo| ≤ 2 ∧
      |(Interval.log2I 384).hi| ≤ 2 := by
    constructor
    · simpa [Interval.log2I, Interval.neg] using hlog2base.2
    · simpa [Interval.log2I, Interval.neg] using hlog2base.1
  have hprod := c5AbsIntervalMulExactEndpoints
    (c := (8 : ℚ)) (M := 2) hlog2.1 hlog2.2
  have hprod' :
      |((Interval.exact (8 : ℚ)).mul (Interval.log2I 384)).lo| ≤ 16 ∧
        |((Interval.exact (8 : ℚ)).mul (Interval.log2I 384)).hi| ≤ 16 := by
    constructor
    · calc
        _ ≤ |(8 : ℚ)| * 2 := hprod.1
        _ = 16 := by norm_num
    · calc
        _ ≤ |(8 : ℚ)| * 2 := hprod.2
        _ = 16 := by norm_num
  rw [Interval.logQ]
  simp only [Interval.add]
  constructor
  · calc
      _ ≤ |((Interval.exact (8 : ℚ)).mul (Interval.log2I 384)).lo| +
          |(Interval.log1 384 (Interval.exact ((240 : ℚ) / 2 ^ 8))).lo| := abs_add_le _ _
      _ ≤ 18 := by linarith [hprod'.1, hlog1'.1]
  · calc
      _ ≤ |((Interval.exact (8 : ℚ)).mul (Interval.log2I 384)).hi| +
          |(Interval.log1 384 (Interval.exact ((240 : ℚ) / 2 ^ 8))).hi| := abs_add_le _ _
      _ ≤ 18 := by linarith [hprod'.2, hlog1'.2]

def c5GammaCoreFirstNodePowerBox : ComplexInterval :=
  ComplexInterval.dirichletTermBox2 384 64 320 8 2 240
    (gammaFiniteNegativePointBox (1 / 5) 0)

def c5GammaCoreFirstNodeFiniteBox : ComplexInterval :=
  c5GammaCoreFirstNodePowerBox.mul c5GammaCoreNodePilotChunkBox

def c5GammaCoreFirstNodeBox : ComplexInterval :=
  c5GammaCoreFirstNodeFiniteBox.inflate (1 / 10 ^ 99)

theorem c5GammaCoreFirstNodePowerArg_normBound :
    ComplexInterval.normBound
      ((gammaFiniteNegativePointBox (1 / 5) 0).neg.mul
        { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 4 := by
  have hlog := c5GammaFirstNode_logQ_absBound
  have hreal := c5AbsIntervalMulExactEndpoints
    (c := (1 / 5 : ℚ)) (M := 18) hlog.1 hlog.2
  unfold gammaFiniteNegativePointBox
  simp only [ComplexInterval.exact, ComplexInterval.neg, Interval.neg,
    Interval.exact, neg_neg]
  change ComplexInterval.normBound
    ((ComplexInterval.exact (1 / 5 : ℚ) 0).mul
      { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 4
  rw [ComplexInterval.normBound, ComplexInterval.mul, ComplexInterval.exact]
  have hzero : (Interval.exact (0 : ℚ)).mul (Interval.exact 0) =
      Interval.exact 0 := by simp [Interval.mul, Interval.exact]
  have hrightzero : (Interval.exact (1 / 5 : ℚ)).mul (Interval.exact 0) =
      Interval.exact 0 := by simp [Interval.mul, Interval.exact]
  have hleftzero : (Interval.exact (0 : ℚ)).mul (Interval.logQ 384 8 240) =
      Interval.exact 0 := by simp [Interval.mul, Interval.exact]
  rw [hzero, hrightzero, hleftzero]
  simp only [Interval.sub, Interval.add, Interval.neg, Interval.exact, neg_zero, add_zero]
  simp only [abs_zero, max_self, add_zero]
  have hbound : (18 : ℚ) / 5 ≤ 4 := by norm_num
  exact (max_le_iff.mpr ⟨hreal.1.trans (by norm_num), hreal.2.trans (by norm_num)⟩).trans hbound

theorem c5GammaCoreFirstNodePowerBox_contains :
    c5GammaCoreFirstNodePowerBox.contains
      ((240 : ℂ) ^ c5GammaCoreFirstNodePoint) := by
  have hS : (gammaFiniteNegativePointBox (1 / 5) 0).contains
      (-c5GammaCoreFirstNodePoint) := by
    change
      Interval.contains (Interval.exact (-(1 / 5 : ℚ)))
          (-c5GammaCoreFirstNodePoint).re ∧
        Interval.contains (Interval.exact (0 : ℚ))
          (-c5GammaCoreFirstNodePoint).im
    constructor
    · simpa [c5GammaCoreFirstNodePoint] using
        Interval.contains_exact (-(1 / 5 : ℚ))
    · simpa [c5GammaCoreFirstNodePoint] using
        Interval.contains_exact (0 : ℚ)
  have hb : ComplexInterval.normBound
      ((gammaFiniteNegativePointBox (1 / 5) 0).neg.mul
        { re := Interval.logQ 384 8 240, im := Interval.exact 0 }) ≤ 2 ^ 2 := by
    calc
      _ ≤ 4 := c5GammaCoreFirstNodePowerArg_normBound
      _ = 2 ^ 2 := by norm_num
  have h := ComplexInterval.contains_dirichletTermBox2
    (nLog := 384) (nExp := 64) (p := 320) (kL := 8) (kE := 2)
    (by norm_num) (by norm_num) (m := 240) (by norm_num)
    (S := gammaFiniteNegativePointBox (1 / 5) 0)
    (s := -c5GammaCoreFirstNodePoint) hS (by norm_num) (by norm_num) hb
  simpa [c5GammaCoreFirstNodePowerBox, c5GammaCoreFirstNodePoint,
    gammaFiniteNegativePointBox] using h

theorem c5GammaCoreFirstNodeBox_contains :
    c5GammaCoreFirstNodeBox.contains
      (Complex.Gamma c5GammaCoreFirstNodePoint) := by
  have hpow := c5GammaCoreFirstNodePowerBox_contains
  have hcore := c5GammaCoreNodePilotChunkBox_contains
  have hfiniteEq :
      gammaFinite 1024 240 c5GammaCoreFirstNodePoint =
        (240 : ℂ) ^ c5GammaCoreFirstNodePoint *
          ratComplexToComplex
            (gammaFiniteRationalCore 1024 240 (1 / 5) 0) := by
    simpa [c5GammaCoreFirstNodePoint] using
      (gammaFinite_eq_rationalCore 1024 240 (1 / 5) 0 (by norm_num))
  have hfinite : c5GammaCoreFirstNodeFiniteBox.contains
      (gammaFinite 1024 240 c5GammaCoreFirstNodePoint) := by
    rw [hfiniteEq]
    simpa [c5GammaCoreFirstNodeFiniteBox, c5GammaCoreNodePilot] using
      ComplexInterval.contains_mul hpow hcore
  have herr := gamma_finite_1024_240_error c5GammaCoreFirstNodePoint
    (by norm_num [c5GammaCoreFirstNodePoint])
    (by norm_num [c5GammaCoreFirstNodePoint])
  have herr' :
      ‖Complex.Gamma c5GammaCoreFirstNodePoint -
        gammaFinite 1024 240 c5GammaCoreFirstNodePoint‖ ≤
          (((1 : ℚ) / 10 ^ 99 : ℚ) : ℝ) := by
    simpa using herr
  exact ComplexInterval.contains_inflate hfinite herr'

#print axioms c5GammaCoreFirstNodePowerBox_contains
#print axioms c5GammaCoreFirstNodeBox_contains

end CarrySigmaObstruction
