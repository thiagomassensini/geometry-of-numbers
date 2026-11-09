import SigmaContour51ArbIntervalComposition
import SigmaC5PiInterval
import ZetaLean.IntervalCExp
import Mathlib.Tactic

/-!
# Lean geometry boxes for the 4096 lower semicircle arcs

This file reuses the C5 rational enclosure of `π`, pushes each exact parameter
arc through the certified complex exponential, and scales the resulting box by
51. It also transports that box through `s = 1/2 + i z`. These are only the
geometric inputs to the Arb component-box structure; they do not enclose ζ,
ζ′, digamma, the response, or the residual integrands.
-/

namespace CarrySigmaObstruction

open ZetaLean ZetaLean.ComplexInterval
open CarrySelfAdjointOperator Complex
open scoped Interval

noncomputable section
set_option autoImplicit false

/-- Tight rational π interval obtained by scaling the already certified C5
quarter-π interval. -/
def contour51C5PiBox : Interval :=
  { lo := c5PiQuarterInterval.lo * 4
    hi := c5PiQuarterInterval.hi * 4
    le := mul_le_mul_of_nonneg_right c5PiQuarterInterval.le (by norm_num) }

theorem contour51C5PiBox_contains : contour51C5PiBox.contains Real.pi := by
  have hquarter := c5_pi_quarter_interval_contains
  constructor
  · change ((c5PiQuarterInterval.lo * 4 : ℚ) : ℝ) ≤ Real.pi
    have h := hquarter.1
    push_cast at h ⊢
    nlinarith
  · change Real.pi ≤ ((c5PiQuarterInterval.hi * 4 : ℚ) : ℝ)
    have h := hquarter.2
    push_cast at h ⊢
    nlinarith

theorem contour51C5PiBox_lower_pos : 0 < contour51C5PiBox.lo := by
  change 0 < c5PiQuarterInterval.lo * 4
  exact mul_pos c5_pi_quarter_interval_pos (by norm_num)

theorem contour51C5PiBox_upper_lt_eight : contour51C5PiBox.hi < 8 := by
  change c5PiQuarterInterval.hi * 4 < 8
  nlinarith [c5_pi_quarter_interval_lt_two]

/-- The rational interval for the parameter `u` of arc `k` in a uniform
partition of `[0,1]` into `N` closed subarcs. -/
def contour51ArcPartitionUBox (N k : ℕ) : Interval :=
  { lo := (k : ℚ) / (N : ℚ)
    hi := ((k + 1 : ℕ) : ℚ) / (N : ℚ)
    le := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (Nat.le_succ k) }

theorem contour51ArcPartitionUBox_contains {N k : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N)) :
    (contour51ArcPartitionUBox N k).contains u := by
  simp only [Interval.contains, contour51ArcPartitionUBox]
  constructor
  · push_cast
    exact hu.1
  · push_cast
    push_cast at hu
    exact hu.2

theorem contour51ArcPartitionUBox_bounds {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    0 ≤ (contour51ArcPartitionUBox N k).lo ∧
      (contour51ArcPartitionUBox N k).hi ≤ 1 := by
  constructor
  · dsimp [contour51ArcPartitionUBox]
    positivity
  · dsimp [contour51ArcPartitionUBox]
    have hk' : k + 1 ≤ N := Nat.succ_le_of_lt hk
    have hkQ : ((k + 1 : ℕ) : ℚ) ≤ (N : ℚ) := by exact_mod_cast hk'
    have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
    rw [div_le_one₀ hNQ]
    exact hkQ

private theorem contour51Interval_mul_unit_bounds {x y : Interval}
    (hx0 : 0 ≤ x.lo) (hx8 : x.hi ≤ 8)
    (hy0 : 0 ≤ y.lo) (hy1 : y.hi ≤ 1) :
    0 ≤ (x.mul y).lo ∧ (x.mul y).hi ≤ 8 := by
  have hxlo : x.lo ≤ 8 := le_trans x.le hx8
  have hylo : y.lo ≤ 1 := le_trans y.le hy1
  have hll0 : 0 ≤ x.lo * y.lo := mul_nonneg hx0 hy0
  have hlh0 : 0 ≤ x.lo * y.hi := mul_nonneg hx0 (le_trans hy0 y.le)
  have hhl0 : 0 ≤ x.hi * y.lo := mul_nonneg (le_trans hx0 x.le) hy0
  have hhh0 : 0 ≤ x.hi * y.hi := mul_nonneg (le_trans hx0 x.le) (le_trans hy0 y.le)
  have hll8 : x.lo * y.lo ≤ 8 := by
    calc
      x.lo * y.lo ≤ x.lo * 1 := mul_le_mul_of_nonneg_left hylo hx0
      _ = x.lo := by ring
      _ ≤ 8 := hxlo
  have hlh8 : x.lo * y.hi ≤ 8 := by
    calc
      x.lo * y.hi ≤ x.lo * 1 := mul_le_mul_of_nonneg_left hy1 hx0
      _ = x.lo := by ring
      _ ≤ 8 := hxlo
  have hhl8 : x.hi * y.lo ≤ 8 := by
    calc
      x.hi * y.lo ≤ x.hi * 1 := mul_le_mul_of_nonneg_left hylo (le_trans hx0 x.le)
      _ = x.hi := by ring
      _ ≤ 8 := hx8
  have hhh8 : x.hi * y.hi ≤ 8 := by
    calc
      x.hi * y.hi ≤ x.hi * 1 := mul_le_mul_of_nonneg_left hy1 (le_trans hx0 x.le)
      _ = x.hi := by ring
      _ ≤ 8 := hx8
  constructor
  · change 0 ≤ min (min (x.lo * y.lo) (x.lo * y.hi))
      (min (x.hi * y.lo) (x.hi * y.hi))
    exact le_min (le_min hll0 hlh0) (le_min hhl0 hhh0)
  · change max (max (x.lo * y.lo) (x.lo * y.hi))
      (max (x.hi * y.lo) (x.hi * y.hi)) ≤ 8
    exact max_le (max_le hll8 hlh8) (max_le hhl8 hhh8)

/-- Complex exponent box for `exp((-πu)I)` on one uniform-partition arc. -/
def contour51ArcPartitionAngleBox (N k : ℕ) : ComplexInterval :=
  { re := Interval.exact 0
    im := ((contour51C5PiBox.mul (contour51ArcPartitionUBox N k)).neg) }

theorem contour51ArcPartitionAngleBox_normBound_le_eight {N k : ℕ}
    (hN : 0 < N) (hk : k < N) :
    ComplexInterval.normBound (contour51ArcPartitionAngleBox N k) ≤ 8 := by
  have hu := contour51ArcPartitionUBox_bounds hN hk
  have hprod := contour51Interval_mul_unit_bounds
    (le_of_lt contour51C5PiBox_lower_pos)
    (le_of_lt contour51C5PiBox_upper_lt_eight) hu.1 hu.2
  have hhi0 : 0 ≤ (contour51C5PiBox.mul (contour51ArcPartitionUBox N k)).hi :=
    le_trans hprod.1 (contour51C5PiBox.mul (contour51ArcPartitionUBox N k)).le
  have hnegHi : -((contour51C5PiBox.mul (contour51ArcPartitionUBox N k)).hi) ≤ 0 := by
    linarith
  have hnegLo : -((contour51C5PiBox.mul (contour51ArcPartitionUBox N k)).lo) ≤ 0 := by
    linarith [hprod.1]
  unfold ComplexInterval.normBound contour51ArcPartitionAngleBox
  simp only [Interval.exact, Interval.neg]
  rw [abs_of_nonpos hnegHi, abs_of_nonpos hnegLo]
  simp only [abs_zero, max_self, zero_add, neg_neg]
  exact max_le hprod.2 (le_trans
    (contour51C5PiBox.mul (contour51ArcPartitionUBox N k)).le hprod.2)

theorem contour51ArcPartitionAngleBox_contains {N k : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N)) :
    (contour51ArcPartitionAngleBox N k).contains
      (((-Real.pi * u : ℝ) : ℂ) * Complex.I) := by
  have huBox := contour51ArcPartitionUBox_contains hu
  have hpiu := Interval.contains_mul contour51C5PiBox_contains huBox
  have hneg := Interval.contains_neg hpiu
  constructor
  · norm_num [contour51ArcPartitionAngleBox, ComplexInterval.contains,
      Interval.contains, Interval.exact, Complex.mul_re, Complex.mul_im]
  · simpa [contour51ArcPartitionAngleBox,
      Complex.mul_re, Complex.mul_im] using hneg

/-- Certified rational box for `z(u) = 51 exp((-πu)I)` on a uniform-partition arc. -/
def contour51ArcPartitionZBox (N k : ℕ) : ComplexInterval :=
  ComplexInterval.smulQ 51
    (ComplexInterval.expCr 32 80 3 (contour51ArcPartitionAngleBox N k))

theorem contour51ArcPartitionZBox_contains {N k : ℕ} (hN : 0 < N) (hk : k < N)
    {u : ℝ} (hu : u ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N)) :
    (contour51ArcPartitionZBox N k).contains (circleMap 0 51 (-Real.pi * u)) := by
  have hexp := ComplexInterval.contains_expCr 32 80 (by norm_num : 0 < 32) 3
    (contour51ArcPartitionAngleBox N k) (((-Real.pi * u : ℝ) : ℂ) * Complex.I)
    (contour51ArcPartitionAngleBox_contains hu)
    (contour51ArcPartitionAngleBox_normBound_le_eight hN hk)
  have hscale := ComplexInterval.contains_smulQ (q := 51) hexp
  simpa [contour51ArcPartitionZBox, circleMap] using hscale

/-- The affine map `s = 1/2 + i z` carries a complex rectangle for `z` to
the corresponding rectangle for `s` on a uniform-partition arc. -/
def contour51ArcPartitionSBox (N k : ℕ) : ComplexInterval :=
  { re := (Interval.exact (1 / 2)).sub (contour51ArcPartitionZBox N k).im
    im := (contour51ArcPartitionZBox N k).re }

theorem contour51ArcPartitionSBox_contains {N k : ℕ} (hN : 0 < N) (hk : k < N)
    {u : ℝ} (hu : u ∈ Set.Icc ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N)) :
    (contour51ArcPartitionSBox N k).contains
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))) := by
  have hz := contour51ArcPartitionZBox_contains hN hk hu
  constructor
  · have hre := operatorHeightParameter_re (circleMap 0 51 (-Real.pi * u))
    rw [hre]
    simpa [contour51ArcPartitionSBox, contour51ArcPartitionZBox] using
      (Interval.contains_sub (Interval.contains_exact (1 / 2)) hz.2)
  · have him := operatorHeightParameter_im (circleMap 0 51 (-Real.pi * u))
    rw [him]
    simpa [contour51ArcPartitionSBox, contour51ArcPartitionZBox] using hz.1

/-- Radius-51 geometric boxes for the 4096 residual arcs. -/
abbrev contour51Arc4096UBox (k : ℕ) : Interval := contour51ArcPartitionUBox 4096 k
abbrev contour51Arc4096AngleBox (k : ℕ) : ComplexInterval :=
  contour51ArcPartitionAngleBox 4096 k
abbrev contour51Arc4096ZBox (k : ℕ) : ComplexInterval := contour51ArcPartitionZBox 4096 k
abbrev contour51Arc4096SBox (k : ℕ) : ComplexInterval := contour51ArcPartitionSBox 4096 k

theorem contour51Arc4096UBox_contains {k : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096)) :
    (contour51Arc4096UBox k).contains u :=
  contour51ArcPartitionUBox_contains hu

theorem contour51Arc4096UBox_bounds {k : ℕ} (hk : k < 4096) :
    0 ≤ (contour51Arc4096UBox k).lo ∧ (contour51Arc4096UBox k).hi ≤ 1 :=
  contour51ArcPartitionUBox_bounds (by norm_num) hk

theorem contour51Arc4096AngleBox_normBound_le_eight {k : ℕ} (hk : k < 4096) :
    ComplexInterval.normBound (contour51Arc4096AngleBox k) ≤ 8 :=
  contour51ArcPartitionAngleBox_normBound_le_eight (by norm_num) hk

theorem contour51Arc4096AngleBox_contains {k : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096)) :
    (contour51Arc4096AngleBox k).contains (((-Real.pi * u : ℝ) : ℂ) * Complex.I) :=
  contour51ArcPartitionAngleBox_contains hu

theorem contour51Arc4096ZBox_contains {k : ℕ} (hk : k < 4096) {u : ℝ}
    (hu : u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096)) :
    (contour51Arc4096ZBox k).contains (circleMap 0 51 (-Real.pi * u)) :=
  contour51ArcPartitionZBox_contains (by norm_num) hk hu

theorem contour51Arc4096SBox_contains {k : ℕ} (hk : k < 4096) {u : ℝ}
    (hu : u ∈ Set.Icc ((k : ℝ) / 4096) (((k + 1 : ℕ) : ℝ) / 4096)) :
    (contour51Arc4096SBox k).contains
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))) :=
  contour51ArcPartitionSBox_contains (by norm_num) hk hu

/-- The same certified geometric enclosure for the 512 arcs used by the uniform
circle-bound certificate. -/
abbrev contour51Arc512ZBox (k : ℕ) : ComplexInterval := contour51ArcPartitionZBox 512 k
abbrev contour51Arc512SBox (k : ℕ) : ComplexInterval := contour51ArcPartitionSBox 512 k

theorem contour51Arc512ZBox_contains {k : ℕ} (hk : k < 512) {u : ℝ}
    (hu : u ∈ Set.Icc ((k : ℝ) / 512) (((k + 1 : ℕ) : ℝ) / 512)) :
    (contour51Arc512ZBox k).contains (circleMap 0 51 (-Real.pi * u)) :=
  contour51ArcPartitionZBox_contains (by norm_num) hk hu

theorem contour51Arc512SBox_contains {k : ℕ} (hk : k < 512) {u : ℝ}
    (hu : u ∈ Set.Icc ((k : ℝ) / 512) (((k + 1 : ℕ) : ℝ) / 512)) :
    (contour51Arc512SBox k).contains
      (operatorHeightParameter (circleMap 0 51 (-Real.pi * u))) :=
  contour51ArcPartitionSBox_contains (by norm_num) hk hu

#print axioms contour51C5PiBox_contains
#print axioms contour51Arc4096AngleBox_normBound_le_eight
#print axioms contour51Arc4096AngleBox_contains
#print axioms contour51Arc4096ZBox_contains
#print axioms contour51Arc4096SBox_contains
#print axioms contour51Arc512ZBox_contains
#print axioms contour51Arc512SBox_contains

end
end CarrySigmaObstruction
