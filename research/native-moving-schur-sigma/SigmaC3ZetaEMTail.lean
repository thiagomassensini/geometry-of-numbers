import SigmaC5EulerMaclaurin
import Mathlib.Tactic

/-!
# A C3-range remainder bound from the reusable C5 Euler--Maclaurin formula

The general Euler--Maclaurin tail theorem already applies in the right half-plane.
This file replaces the C5 node-only bound `‖s‖ ≤ 1` with a kernel-checked
Pochhammer product estimate valid when `‖s‖ ≤ 54`, a region large enough for
radius-51 contour points and a small neighborhood of them. The Bernoulli table
and the Euler--Maclaurin identity are imported unchanged.
-/

namespace CarrySigmaObstruction

open SigmaC5Zeta
open scoped BigOperators

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000

/-- Per-factor growth allowance for `(s)_600`, split into four finite ranges. -/
private def c3PochhammerGrowthPower (j : ℕ) : ℕ :=
  if j < 10 then 6 else if j < 30 then 3 else if j < 52 then 2 else 1

private theorem c3PochhammerGrowthPower_sum :
    ∑ j ∈ Finset.range 600, c3PochhammerGrowthPower j = 712 := by
  norm_num [c3PochhammerGrowthPower, Finset.sum_range_succ]

/-- On `‖s‖≤54`, the 600-factor Pochhammer product is at most `600!·2^712`.
The exponent is obtained by grouping small indices, where `j+54` is relatively
large compared with `j+1`, and using a factor of two after index 52. -/
theorem c3_emPochhammer_norm_le_factorial_mul_two_pow
    {s : ℂ} (hs : ‖s‖ ≤ 54) :
    ‖emPochhammer s 600‖ ≤ (Nat.factorial 600 : ℝ) * 2 ^ 712 := by
  have hterm : ∀ j ∈ Finset.range 600,
      ‖s + (j : ℂ)‖ ≤ ((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ c3PochhammerGrowthPower j := by
    intro j hj
    have hjlt : j < 600 := Finset.mem_range.mp hj
    have hjR : (j : ℝ) ≤ 599 := by exact_mod_cast (Nat.lt_succ_iff.mp hjlt)
    have hbase : ‖s + (j : ℂ)‖ ≤ 54 + (j : ℝ) := by
      calc
        ‖s + (j : ℂ)‖ ≤ ‖s‖ + ‖(j : ℂ)‖ := norm_add_le _ _
        _ = ‖s‖ + (j : ℝ) := by simp
        _ ≤ 54 + (j : ℝ) := by nlinarith [hs]
    by_cases hj10 : j < 10
    · have hjRF : (0 : ℝ) ≤ (j : ℝ) := by positivity
      simp [c3PochhammerGrowthPower, hj10]
      norm_num
      nlinarith
    · by_cases hj30 : j < 30
      · have hj10R : (10 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.le_of_not_gt hj10)
        simp [c3PochhammerGrowthPower, hj10, hj30]
        norm_num
        nlinarith
      · by_cases hj52 : j < 52
        · have hj30R : (30 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.le_of_not_gt hj30)
          simp [c3PochhammerGrowthPower, hj10, hj30, hj52]
          norm_num
          nlinarith
        · have hj52R : (52 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.le_of_not_gt hj52)
          simp [c3PochhammerGrowthPower, hj10, hj30, hj52]
          nlinarith
  have hfactorial :
      (∏ j ∈ Finset.range 600, ((j + 1 : ℕ) : ℝ)) = (Nat.factorial 600 : ℝ) := by
    exact_mod_cast (Finset.prod_range_add_one_eq_factorial 600)
  have hgrowth :
      ∏ j ∈ Finset.range 600, (2 : ℝ) ^ c3PochhammerGrowthPower j = (2 : ℝ) ^ 712 := by
    rw [Finset.prod_pow_eq_pow_sum, c3PochhammerGrowthPower_sum]
  calc
    ‖emPochhammer s 600‖ =
        ∏ j ∈ Finset.range 600, ‖s + (j : ℂ)‖ := by simp [emPochhammer, norm_prod]
    _ ≤ ∏ j ∈ Finset.range 600,
        (((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ c3PochhammerGrowthPower j) := by
      apply Finset.prod_le_prod
      · intro j hj
        exact norm_nonneg _
      · intro j hj
        exact hterm j hj
    _ = (∏ j ∈ Finset.range 600, ((j + 1 : ℕ) : ℝ)) *
        (∏ j ∈ Finset.range 600, (2 : ℝ) ^ c3PochhammerGrowthPower j) := by
      rw [Finset.prod_mul_distrib]
    _ = (Nat.factorial 600 : ℝ) * 2 ^ 712 := by rw [hfactorial, hgrowth]

/-- The C5 Euler--Maclaurin tail has a strict `10^-40` bound throughout the
right half-plane portion with `‖s‖≤54`. This is a value-tail estimate; a
separate derivative-tail estimate is still needed to enclose ζ′. -/
theorem c3_emZetaHighTail_norm_lt
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hsNorm : ‖s‖ ≤ 54) :
    ‖∑' k : ℕ, emZetaHighBlock s 300 ((k + 100 : ℕ) : ℝ)‖ < 1 / 10 ^ 40 := by
  have htail := emZetaHighTail_norm_le hs hs1 (P := 300) (N := 100)
    (by norm_num) (by norm_num)
  have hpoch := c3_emPochhammer_norm_le_factorial_mul_two_pow hsNorm
  have hpow600 : (100 : ℝ) ^ (-(600 : ℝ)) = (100 ^ 600 : ℝ)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 100) (600 : ℝ)]
    have harg : (600 : ℝ) = (600 : ℕ) := by norm_num
    rw [harg, Real.rpow_natCast]
  have hpow599 : (100 : ℝ) ^ (-(599 : ℝ)) = (100 ^ 599 : ℝ)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 100) (599 : ℝ)]
    have harg : (599 : ℝ) = (599 : ℕ) := by norm_num
    rw [harg, Real.rpow_natCast]
  have hq1 : (599 : ℝ) ≤ s.re + 600 - 1 := by linarith
  have hpow0 : (100 : ℝ) ^ (-(s.re + (600 : ℝ))) ≤
      (100 : ℝ) ^ (-(600 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 100)
    linarith
  have hpow1 : (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) ≤
      (100 : ℝ) ^ (-599 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 100)
    linarith
  have hinv : (s.re + 600 - 1)⁻¹ ≤ (599 : ℝ)⁻¹ := by
    exact inv_anti₀ (by norm_num) hq1
  have htailSum :
      (100 : ℝ) ^ (-(s.re + (600 : ℝ))) +
        (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) / (s.re + 600 - 1) ≤
      (100 : ℝ) ^ (-(600 : ℝ)) + (100 : ℝ) ^ (-(599 : ℝ)) / 599 := by
    apply add_le_add hpow0
    calc
      (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) / (s.re + 600 - 1) =
          (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) * (s.re + 600 - 1)⁻¹ := by
            rw [div_eq_mul_inv]
      _ ≤ (100 : ℝ) ^ (-599) * (599 : ℝ)⁻¹ :=
        mul_le_mul hpow1 hinv (by positivity) (by positivity)
      _ = (100 : ℝ) ^ (-(599 : ℝ)) / 599 := by rw [div_eq_mul_inv]
  have hrat :
      (4 / (6 : ℝ) ^ 600) * (Nat.factorial 600 : ℝ) * (2 : ℝ) ^ 712 *
        ((100 : ℝ) ^ (-(600 : ℝ)) +
          (100 : ℝ) ^ (-(599 : ℝ)) / 599) < 1 / (10 ^ 40 : ℝ) := by
    rw [hpow600, hpow599]
    have hnat : 2796 * Nat.factorial 600 * 2 ^ 712 * 10 ^ 40 <
        599 * 6 ^ 600 * 100 ^ 600 := by
      norm_num [Nat.factorial]
    have hnatR : (2796 : ℝ) * (Nat.factorial 600 : ℝ) * 2 ^ 712 * 10 ^ 40 <
        599 * 6 ^ 600 * 100 ^ 600 := by exact_mod_cast hnat
    have hratioR :
        (2796 : ℝ) * (Nat.factorial 600 : ℝ) * 2 ^ 712 /
            (599 * 6 ^ 600 * 100 ^ 600) < 1 / (10 ^ 40 : ℝ) := by
      exact (div_lt_div_iff₀ (by positivity) (by positivity)).2 (by
        simpa [mul_assoc] using hnatR)
    calc
      _ = (2796 : ℝ) * (Nat.factorial 600 : ℝ) * 2 ^ 712 /
          (599 * 6 ^ 600 * 100 ^ 600) := by field_simp; ring
      _ < 1 / (10 ^ 40 : ℝ) := hratioR
  have htail' :
      ‖∑' k : ℕ, emZetaHighBlock s 300 ((k + 100 : ℕ) : ℝ)‖ ≤
        (4 / (6 : ℝ) ^ 600) * ‖emPochhammer s 600‖ *
          ((100 : ℝ) ^ (-(s.re + (600 : ℝ))) +
            (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) / (s.re + 600 - 1)) := by
    simpa using htail
  have hmul :
      (4 / (6 : ℝ) ^ 600) * ‖emPochhammer s 600‖ *
        ((100 : ℝ) ^ (-(s.re + (600 : ℝ))) +
          (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) / (s.re + 600 - 1)) ≤
      (4 / (6 : ℝ) ^ 600) * (Nat.factorial 600 : ℝ) * (2 : ℝ) ^ 712 *
        ((100 : ℝ) ^ (-(600 : ℝ)) +
          (100 : ℝ) ^ (-(599 : ℝ)) / 599) := by
    have hcoeff : 0 ≤ (4 / (6 : ℝ) ^ 600) := by positivity
    have hcore :
        ‖emPochhammer s 600‖ *
          ((100 : ℝ) ^ (-(s.re + (600 : ℝ))) +
            (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) / (s.re + 600 - 1)) ≤
        ((Nat.factorial 600 : ℝ) * (2 : ℝ) ^ 712) *
          ((100 : ℝ) ^ (-(600 : ℝ)) +
            (100 : ℝ) ^ (-(599 : ℝ)) / 599) := by
      exact mul_le_mul hpoch htailSum (by positivity) (by positivity)
    calc
      _ = (4 / (6 : ℝ) ^ 600) *
          (‖emPochhammer s 600‖ *
            ((100 : ℝ) ^ (-(s.re + (600 : ℝ))) +
              (100 : ℝ) ^ (1 - (s.re + (600 : ℝ))) / (s.re + 600 - 1))) := by ring
      _ ≤ (4 / (6 : ℝ) ^ 600) *
          (((Nat.factorial 600 : ℝ) * (2 : ℝ) ^ 712) *
            ((100 : ℝ) ^ (-(600 : ℝ)) +
              (100 : ℝ) ^ (-(599 : ℝ)) / 599)) :=
        mul_le_mul_of_nonneg_left hcore hcoeff
      _ = _ := by ring
  exact lt_of_le_of_lt (le_trans htail' hmul) hrat

#print axioms c3_emPochhammer_norm_le_factorial_mul_two_pow
#print axioms c3_emZetaHighTail_norm_lt

end
end CarrySigmaObstruction
