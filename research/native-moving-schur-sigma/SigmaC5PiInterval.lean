import SigmaC5PiBounds
import ZetaLean.IntervalExp

/-!
# Carry the formal π enclosure into rational interval arithmetic

The C5 source uses `log π` in the original archimedean completion. This module
turns the exact rational Machin enclosure into a certified interval for that
real logarithm, using the existing kernel-checked `ZetaLean.Interval` log
series and its `log 2` anchor.
-/

namespace CarrySigmaObstruction

open ZetaLean

theorem c5_pi_error_lt_quarter : c5PiError < (1 / 4 : ℚ) := by
  have hpow5 : (1 / 5 : ℚ) ^ 341 ≤ (1 / 5 : ℚ) ^ 5 := by
    rw [show (341 : ℕ) = 5 + 336 by norm_num, pow_add]
    calc
      (1 / 5 : ℚ) ^ 5 * (1 / 5 : ℚ) ^ 336 ≤
          (1 / 5 : ℚ) ^ 5 * 1 :=
        mul_le_mul_of_nonneg_left
          (pow_le_one₀ (by norm_num : (0 : ℚ) ≤ 1 / 5)
            (by norm_num : (1 / 5 : ℚ) ≤ 1)) (by positivity)
      _ = (1 / 5 : ℚ) ^ 5 := by ring
  have hpow239 : (1 / 239 : ℚ) ^ 111 ≤ (1 / 239 : ℚ) := by
    rw [show (111 : ℕ) = 1 + 110 by norm_num, pow_add, pow_one]
    calc
      (1 / 239 : ℚ) * (1 / 239 : ℚ) ^ 110 ≤
          (1 / 239 : ℚ) * 1 :=
        mul_le_mul_of_nonneg_left
          (pow_le_one₀ (by norm_num : (0 : ℚ) ≤ 1 / 239)
            (by norm_num : (1 / 239 : ℚ) ≤ 1)) (by positivity)
      _ = (1 / 239 : ℚ) := by ring
  have hrem5 : c5AtanRemainder 170 (1 / 5) ≤ (1 / 5 : ℚ) ^ 5 := by
    change (1 / 5 : ℚ) ^ 341 / (2 * 170 + 1) ≤ (1 / 5 : ℚ) ^ 5
    calc
      (1 / 5 : ℚ) ^ 341 / (2 * 170 + 1) ≤ (1 / 5 : ℚ) ^ 341 :=
        div_le_self (by positivity) (by norm_num)
      _ ≤ (1 / 5 : ℚ) ^ 5 := hpow5
  have hrem239 : c5AtanRemainder 55 (1 / 239) ≤ (1 / 239 : ℚ) := by
    change (1 / 239 : ℚ) ^ 111 / (2 * 55 + 1) ≤ (1 / 239 : ℚ)
    calc
      (1 / 239 : ℚ) ^ 111 / (2 * 55 + 1) ≤ (1 / 239 : ℚ) ^ 111 :=
        div_le_self (by positivity) (by norm_num)
      _ ≤ (1 / 239 : ℚ) := hpow239
  dsimp [c5PiError]
  calc
    16 * c5AtanRemainder 170 (1 / 5) +
        4 * c5AtanRemainder 55 (1 / 239) ≤
      16 * (1 / 5 : ℚ) ^ 5 + 4 * (1 / 239 : ℚ) := by
        gcongr
    _ < 1 / 100 + 1 / 50 := by norm_num
    _ < 1 / 4 := by norm_num

theorem c5PiError_nonneg : 0 ≤ c5PiError := by
  unfold c5PiError c5AtanRemainder
  positivity

def c5PiQuarterInterval : Interval :=
  { lo := (c5PiCenter - c5PiError) / 4
    hi := (c5PiCenter + c5PiError) / 4
    le := by
      rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 4)]
      linarith [c5PiError_nonneg] }

theorem c5_pi_quarter_interval_contains :
    c5PiQuarterInterval.contains (Real.pi / 4) := by
  have hpi := abs_le.mp c5_pi_rational_enclosure
  constructor
  · change (((c5PiCenter - c5PiError) / 4 : ℚ) : ℝ) ≤ Real.pi / 4
    push_cast
    linarith
  · change Real.pi / 4 ≤
      (((c5PiCenter + c5PiError) / 4 : ℚ) : ℝ)
    push_cast
    linarith

theorem c5_pi_quarter_interval_pos : 0 < c5PiQuarterInterval.lo := by
  have hpi := abs_le.mp c5_pi_rational_enclosure
  have he := c5_pi_error_lt_quarter
  have heR : (c5PiError : ℝ) < ((1 / 4 : ℚ) : ℝ) := by exact_mod_cast he
  have hloR : (1 / 4 : ℝ) <
      (((c5PiCenter - c5PiError) / 4 : ℚ) : ℝ) := by
    push_cast
    nlinarith [Real.two_le_pi]
  change (0 : ℚ) < (c5PiCenter - c5PiError) / 4
  have hloPos := lt_trans (by norm_num : (0 : ℝ) < 1 / 4) hloR
  exact_mod_cast hloPos

theorem c5_pi_quarter_interval_lt_two : c5PiQuarterInterval.hi < 2 := by
  have hpi := abs_le.mp c5_pi_rational_enclosure
  have he := c5_pi_error_lt_quarter
  have heR : (c5PiError : ℝ) < ((1 / 4 : ℚ) : ℝ) := by exact_mod_cast he
  have hhiR :
      (((c5PiCenter + c5PiError) / 4 : ℚ) : ℝ) < 2 := by
    push_cast
    have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
    nlinarith [Real.pi_le_four]
  change (c5PiCenter + c5PiError) / 4 < 2
  exact_mod_cast hhiR

def c5PiLogInterval (n : ℕ) : Interval :=
  (Interval.log1 n c5PiQuarterInterval).add
    ((Interval.exact 2).mul (Interval.log2I n))

theorem c5_pi_log_interval_contains (n : ℕ) :
    (c5PiLogInterval n).contains (Real.log Real.pi) := by
  have hquarter := c5_pi_quarter_interval_contains
  have hlogQuarter := Interval.contains_log1 (n := n) hquarter
    c5_pi_quarter_interval_pos c5_pi_quarter_interval_lt_two
  have hlogTwo := Interval.contains_log2I n
  have htwice := Interval.contains_mul (Interval.contains_exact (2 : ℚ)) hlogTwo
  have hadd := Interval.contains_add hlogQuarter htwice
  have hidentity : Real.log Real.pi =
      Real.log (Real.pi / 4) + 2 * Real.log 2 := by
    have hmul := Real.log_mul (by positivity : Real.pi / 4 ≠ 0)
      (by norm_num : (4 : ℝ) ≠ 0)
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    calc
      Real.log Real.pi = Real.log ((Real.pi / 4) * 4) := by congr 1; ring
      _ = Real.log (Real.pi / 4) + Real.log 4 := hmul
      _ = Real.log (Real.pi / 4) + 2 * Real.log 2 := by rw [hlog4]
  rw [hidentity]
  exact hadd

end CarrySigmaObstruction
