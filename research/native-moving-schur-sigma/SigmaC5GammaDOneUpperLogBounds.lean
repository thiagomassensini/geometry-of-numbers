import SigmaC5GammaSecondRealPointGammaCertificate
import Mathlib.Tactic

namespace CarrySigmaObstruction
open ZetaLean ZetaLean.ComplexInterval
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

private theorem d1_sum_geom_half (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 1)) = 1 - (1 / 2 : ℚ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

private theorem d1_sum_split_first (f : ℕ → ℚ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), f i) =
      f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ i ∈ Finset.range ((n + 1) + 1), f i) =
            (∑ i ∈ Finset.range (n + 1), f i) + f (n + 1) := by
              rw [Finset.sum_range_succ]
        _ = (f 0 + ∑ i ∈ Finset.range n, f (i + 1)) + f (n + 1) := by rw [ih]
        _ = f 0 + ∑ i ∈ Finset.range (n + 1), f (i + 1) := by
              rw [Finset.sum_range_succ]
              ring

private theorem d1_sum_geom_half_shift (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 2)) =
      (1 / 2 : ℚ) * (1 - (1 / 2 : ℚ) ^ n) := by
  calc
    (∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 2)) =
        (1 / 2 : ℚ) * ∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_succ]
          ring
    _ = (1 / 2 : ℚ) * (1 - (1 / 2 : ℚ) ^ n) := by rw [d1_sum_geom_half]

private theorem d1_logSum_half_le_three_quarters (n : ℕ) :
    |Interval.logSum n (1 / 2)| ≤ 3 / 4 := by
  cases n with
  | zero => norm_num [Interval.logSum]
  | succ n =>
      rw [Interval.logSum, d1_sum_split_first]
      simp only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, Nat.cast_zero, Nat.zero_add, Nat.reduceAdd, pow_one]
      have htail :
          |∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 2) / ((i : ℚ) + 1 + 1)| ≤ 1 / 4 := by
        calc
          |∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 2) / ((i : ℚ) + 1 + 1)| ≤
              ∑ i ∈ Finset.range n, |(1 / 2 : ℚ) ^ (i + 2) / ((i : ℚ) + 1 + 1)| :=
                Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 2) / 2 := by
                apply Finset.sum_le_sum
                intro i hi
                rw [abs_div, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ (i + 2)),
                  abs_of_nonneg (by positivity : (0 : ℚ) ≤ (i : ℚ) + 1 + 1)]
                have hden : (2 : ℚ) ≤ (i : ℚ) + 1 + 1 := by
                  exact_mod_cast (show 2 ≤ i + 2 by omega)
                gcongr
          _ = (1 / 2 : ℚ) * ∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 2) := by
                calc
                  _ = ∑ i ∈ Finset.range n, (1 / 2 : ℚ) * (1 / 2 : ℚ) ^ (i + 2) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
                  _ = _ := by rw [Finset.mul_sum]
          _ = (1 / 2 : ℚ) * ((1 / 2 : ℚ) * (1 - (1 / 2 : ℚ) ^ n)) := by
                rw [d1_sum_geom_half_shift]
          _ ≤ 1 / 4 := by
                have hp : 0 ≤ (1 / 2 : ℚ) ^ n := pow_nonneg (by norm_num) _
                have hp' : (1 / 2 : ℚ) ^ n ≤ 1 := by
                  exact pow_le_one₀ (by norm_num) (by norm_num)
                nlinarith
      calc
        |(1 / 2 : ℚ) / ((0 : ℚ) + 1) +
            ∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 2) / ((i : ℚ) + 1 + 1)| ≤
            |(1 / 2 : ℚ) / ((0 : ℚ) + 1)| +
              |∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 2) / ((i : ℚ) + 1 + 1)| := abs_add_le _ _
        _ ≤ 3 / 4 := by
          norm_num at htail ⊢; linarith

private theorem d1_logRem_half_le_one (n : ℕ) {q : ℚ} (hq : |q| ≤ 1 / 2) :
    |Interval.logRem n q| ≤ 1 := by
  unfold Interval.logRem
  have hden : 0 < 1 - |q| := by linarith [abs_nonneg q]
  rw [abs_of_nonneg (div_nonneg (pow_nonneg (abs_nonneg q) _) (le_of_lt hden))]
  rw [div_le_iff₀ hden]
  have hnum : |q| ^ (n + 1) ≤ (1 / 2 : ℚ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg q) hq _
  have hhalf : (1 / 2 : ℚ) ^ (n + 1) ≤ 1 / 2 :=
    pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  nlinarith [hnum, hhalf, abs_nonneg q]

private theorem d1_abs_max_le {x y M : ℚ} (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |max x y| ≤ M := by
  apply abs_le.mpr
  constructor
  · exact (abs_le.mp hx).1.trans (le_max_left x y)
  · exact max_le (abs_le.mp hx).2 (abs_le.mp hy).2

private theorem d1_log1_half_abs_endpoints :
    |(Interval.log1 384 (Interval.exact (1 / 2))).lo| ≤ 1 ∧
      |(Interval.log1 384 (Interval.exact (1 / 2))).hi| ≤ 1 := by
  have hs := d1_logSum_half_le_three_quarters 384
  have hrem_eq : Interval.logRem 384 (1 / 2 : ℚ) = (1 / 2 : ℚ) ^ 384 := by
    rw [Interval.logRem, abs_of_pos (by norm_num : (0 : ℚ) < 1 / 2), pow_succ]
    norm_num
  have hp : (1 / 2 : ℚ) ^ 384 ≤ (1 / 2 : ℚ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  have hr : |Interval.logRem 384 (1 / 2 : ℚ)| ≤ 1 / 4 := by
    calc
      _ = (1 / 2 : ℚ) ^ 384 := by
        rw [hrem_eq, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℚ) ≤ (1 / 2 : ℚ)) 384)]
      _ ≤ (1 / 2 : ℚ) ^ 2 := hp
      _ = 1 / 4 := by norm_num
  have hlo : |-Interval.logSum 384 (1 / 2) - Interval.logRem 384 (1 / 2)| ≤ 1 := by
    calc
      _ ≤ |Interval.logSum 384 (1 / 2)| + |Interval.logRem 384 (1 / 2)| := by
        rw [show -Interval.logSum 384 (1 / 2) - Interval.logRem 384 (1 / 2) =
          -(Interval.logSum 384 (1 / 2) + Interval.logRem 384 (1 / 2)) by ring, abs_neg]
        exact abs_add_le _ _
      _ ≤ 1 := by linarith
  have hhi0 : |-Interval.logSum 384 (1 / 2) + Interval.logRem 384 (1 / 2)| ≤ 1 := by
    calc
      _ ≤ |Interval.logSum 384 (1 / 2)| + |Interval.logRem 384 (1 / 2)| := by
        simpa [abs_neg] using (abs_add_le (-Interval.logSum 384 (1 / 2)) (Interval.logRem 384 (1 / 2)))
      _ ≤ 1 := by linarith
  constructor
  · norm_num [Interval.log1, Interval.exact]
    exact hlo
  · norm_num [Interval.log1, Interval.exact]
    exact d1_abs_max_le hhi0 hlo

theorem c5GammaDOneUpper_log2I_absBound :
    |(Interval.log2I 384).lo| ≤ 1 ∧ |(Interval.log2I 384).hi| ≤ 1 := by
  have h := d1_log1_half_abs_endpoints
  constructor
  · simpa [Interval.log2I, Interval.neg] using h.2
  · simpa [Interval.log2I, Interval.neg] using h.1

private theorem d1_abs_logSum_half {n : ℕ} {q : ℚ}
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
    _ = 1 - (1 / 2 : ℚ) ^ n := d1_sum_geom_half n
    _ ≤ 1 := by
      have hn : 0 ≤ (1 / 2 : ℚ) ^ n := pow_nonneg (by norm_num) _
      linarith

private theorem d1_abs_logRem_half {n : ℕ} {q : ℚ}
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

private theorem d1_log1_abs_endpoints (n : ℕ) (x : ℚ)
    (hq : |1 - x| ≤ 1 / 2) :
    |(Interval.log1 n (Interval.exact x)).lo| ≤ 2 ∧
      |(Interval.log1 n (Interval.exact x)).hi| ≤ 2 := by
  have hs := d1_abs_logSum_half (n := n) (q := 1 - x) hq
  have hr := d1_abs_logRem_half (n := n) (q := 1 - x) hq
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
    exact d1_abs_max_le hhi0 hlo

theorem c5GammaDOneUpper_logQ_absBound :
    |(Interval.logQ 384 8 240).lo| ≤ 10 ∧
      |(Interval.logQ 384 8 240).hi| ≤ 10 := by
  have hlog2 := c5GammaDOneUpper_log2I_absBound
  have hprod := c5AbsIntervalMulExactEndpoints
    (c := (8 : ℚ)) (M := 1) hlog2.1 hlog2.2
  have hprod' :
      |((Interval.exact (8 : ℚ)).mul (Interval.log2I 384)).lo| ≤ 8 ∧
        |((Interval.exact (8 : ℚ)).mul (Interval.log2I 384)).hi| ≤ 8 := by
    constructor
    · calc
        _ ≤ |(8 : ℚ)| * 1 := hprod.1
        _ = 8 := by norm_num
    · calc
        _ ≤ |(8 : ℚ)| * 1 := hprod.2
        _ = 8 := by norm_num
  have hq : |1 - (240 : ℚ) / 2 ^ 8| ≤ 1 / 2 := by norm_num
  have hlog1 := d1_log1_abs_endpoints 384 ((240 : ℚ) / 2 ^ 8) hq
  rw [Interval.logQ]
  simp only [Interval.add]
  constructor
  · calc
      _ ≤ |((Interval.exact (8 : ℚ)).mul (Interval.log2I 384)).lo| +
          |(Interval.log1 384 (Interval.exact ((240 : ℚ) / 2 ^ 8))).lo| := abs_add_le _ _
      _ ≤ 10 := by linarith [hprod'.1, hlog1.1]
  · calc
      _ ≤ |((Interval.exact (8 : ℚ)).mul (Interval.log2I 384)).hi| +
          |(Interval.log1 384 (Interval.exact ((240 : ℚ) / 2 ^ 8))).hi| := abs_add_le _ _
      _ ≤ 10 := by linarith [hprod'.2, hlog1.2]

#print axioms c5GammaDOneUpper_log2I_absBound
#print axioms c5GammaDOneUpper_logQ_absBound

end CarrySigmaObstruction
