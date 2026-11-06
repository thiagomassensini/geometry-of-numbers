import Mathlib.Analysis.Real.Pi.Leibniz

/-!
# Rational enclosures for C5 constants

This file develops a kernel-checkable alternating-series enclosure for
`Real.arctan` at rational points. The next step uses Machin's formula to obtain
the high-precision rational bounds for `Real.pi` needed by source evaluation.
-/

namespace CarrySigmaObstruction

open Finset

def c5AtanPartial (N : ℕ) (q : ℚ) : ℚ :=
  ∑ n ∈ Finset.range N, (-1 : ℚ) ^ n * q ^ (2 * n + 1) / (2 * n + 1)

def c5AtanRemainder (N : ℕ) (q : ℚ) : ℚ :=
  q ^ (2 * N + 1) / (2 * N + 1)

private noncomputable def c5AtanTerm (q : ℝ) (n : ℕ) : ℝ :=
  q ^ (2 * n + 1) / (2 * n + 1)

private theorem c5AtanTerm_antitone {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Antitone (c5AtanTerm q) := by
  intro m n hmn
  change q ^ (2 * n + 1) / (2 * n + 1) ≤
    q ^ (2 * m + 1) / (2 * m + 1)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have he : 2 * m + 1 ≤ 2 * n + 1 := by omega
  have hpow : q ^ (2 * n + 1) ≤ q ^ (2 * m + 1) :=
    pow_le_pow_of_le_one hq0 hq1 he
  have hden : (2 * n + 1 : ℝ)⁻¹ ≤ (2 * m + 1 : ℝ)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact_mod_cast he
  exact mul_le_mul hpow hden (by positivity) (by positivity)

private theorem c5AtanTerm_summable {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (c5AtanTerm q) := by
  have hgeom : Summable (fun n : ℕ => q * (q ^ 2) ^ n) := by
    have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
    have hq2lt : q ^ 2 < 1 := by nlinarith
    exact (summable_geometric_of_lt_one hq2 hq2lt).mul_left q
  apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeom
  · change 0 ≤ q ^ (2 * n + 1) / (2 * n + 1)
    exact div_nonneg (pow_nonneg hq0 _) (by positivity)
  · change q ^ (2 * n + 1) / (2 * n + 1) ≤ q * (q ^ 2) ^ n
    have hn : (1 : ℝ) ≤ (2 * n + 1 : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
    have hpow : q ^ (2 * n + 1) = q * (q ^ 2) ^ n := by
      rw [pow_succ, pow_mul]
      ring
    rw [hpow]
    exact div_le_self (by positivity) hn

private theorem c5AtanPartial_cast (N : ℕ) (q : ℚ) :
    ((c5AtanPartial N q : ℚ) : ℝ) =
      ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n *
        (q : ℝ) ^ (2 * n + 1) / (2 * n + 1) := by
  simp [c5AtanPartial]

theorem c5_arctan_partial_enclosure {N : ℕ} {q : ℚ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    |Real.arctan (q : ℝ) - (c5AtanPartial N q : ℝ)| ≤
      (c5AtanRemainder N q : ℝ) := by
  have hq0' : 0 ≤ (q : ℝ) := by exact_mod_cast hq0
  have hq1' : (q : ℝ) < 1 := by exact_mod_cast hq1
  have hnorm : ‖(q : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0']
    exact hq1'
  let f : ℕ → ℝ := c5AtanTerm (q : ℝ)
  have hsum : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * f n)
      (Real.arctan (q : ℝ)) := by
    simpa [f, c5AtanTerm, div_eq_mul_inv, mul_assoc] using
      (Real.hasSum_arctan hnorm)
  have hanti : Antitone f := c5AtanTerm_antitone hq0' hq1'.le
  have hfs : Summable f := c5AtanTerm_summable hq0' hq1'
  have herr := alternating_series_error_bound f hanti hfs N
  rw [hsum.tsum_eq] at herr
  have hpartial : (c5AtanPartial N q : ℝ) =
      ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * f n := by
    simpa only [f, c5AtanTerm, mul_div_assoc] using
      (c5AtanPartial_cast N q)
  rw [← hpartial] at herr
  have hrem : (c5AtanRemainder N q : ℝ) = f N := by
    simp [c5AtanRemainder, f, c5AtanTerm]
  rw [← hrem] at herr
  simpa [sub_eq_add_neg, abs_sub_comm] using herr

def c5PiCenter : ℚ :=
  16 * c5AtanPartial 170 (1 / 5) - 4 * c5AtanPartial 55 (1 / 239)

def c5PiError : ℚ :=
  16 * c5AtanRemainder 170 (1 / 5) + 4 * c5AtanRemainder 55 (1 / 239)

/-- A rational enclosure for π obtained from Machin's identity and the
alternating arctangent series. -/
theorem c5_pi_rational_enclosure :
    |Real.pi - (c5PiCenter : ℝ)| ≤ (c5PiError : ℝ) := by
  have hq5 : ((1 / 5 : ℚ) : ℝ) = (5 : ℝ)⁻¹ := by norm_num
  have hq239 : ((1 / 239 : ℚ) : ℝ) = (239 : ℝ)⁻¹ := by norm_num
  have hmachin :
      4 * Real.arctan ((1 / 5 : ℚ) : ℝ) -
        Real.arctan ((1 / 239 : ℚ) : ℝ) = Real.pi / 4 := by
    rw [hq5, hq239]
    exact Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hpi : Real.pi =
      16 * Real.arctan ((1 / 5 : ℚ) : ℝ) -
        4 * Real.arctan ((1 / 239 : ℚ) : ℝ) := by
    linarith
  have h5 := c5_arctan_partial_enclosure (N := 170) (q := (1 / 5 : ℚ))
    (by norm_num) (by norm_num)
  have h239 := c5_arctan_partial_enclosure (N := 55) (q := (1 / 239 : ℚ))
    (by norm_num) (by norm_num)
  have h5mul :
      |16 * (Real.arctan ((1 / 5 : ℚ) : ℝ) -
        (c5AtanPartial 170 (1 / 5) : ℝ))| ≤
        16 * (c5AtanRemainder 170 (1 / 5) : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
    exact mul_le_mul_of_nonneg_left h5 (by norm_num)
  have h239mul :
      |4 * (Real.arctan ((1 / 239 : ℚ) : ℝ) -
        (c5AtanPartial 55 (1 / 239) : ℝ))| ≤
        4 * (c5AtanRemainder 55 (1 / 239) : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    exact mul_le_mul_of_nonneg_left h239 (by norm_num)
  have hdecomp : Real.pi - (c5PiCenter : ℝ) =
      16 * (Real.arctan ((1 / 5 : ℚ) : ℝ) -
        (c5AtanPartial 170 (1 / 5) : ℝ)) -
      4 * (Real.arctan ((1 / 239 : ℚ) : ℝ) -
        (c5AtanPartial 55 (1 / 239) : ℝ)) := by
    rw [hpi, c5PiCenter]
    push_cast
    ring
  rw [hdecomp, c5PiError]
  calc
    |16 * (Real.arctan ((1 / 5 : ℚ) : ℝ) -
        (c5AtanPartial 170 (1 / 5) : ℝ)) -
      4 * (Real.arctan ((1 / 239 : ℚ) : ℝ) -
        (c5AtanPartial 55 (1 / 239) : ℝ))|
        ≤ |16 * (Real.arctan ((1 / 5 : ℚ) : ℝ) -
            (c5AtanPartial 170 (1 / 5) : ℝ))| +
          |4 * (Real.arctan ((1 / 239 : ℚ) : ℝ) -
            (c5AtanPartial 55 (1 / 239) : ℝ))| := abs_sub _ _
    _ ≤ 16 * (c5AtanRemainder 170 (1 / 5) : ℝ) +
        4 * (c5AtanRemainder 55 (1 / 239) : ℝ) := add_le_add h5mul h239mul
    _ = (c5PiError : ℝ) := by simp [c5PiError]

end CarrySigmaObstruction
