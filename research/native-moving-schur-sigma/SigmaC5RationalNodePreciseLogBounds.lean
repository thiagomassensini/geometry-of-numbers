import SigmaC5RationalNodeLogBounds

namespace CarrySigmaObstruction

open ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false

/-- Center each binary reduction around one.  Unlike ceiling log2, this keeps
the argument of `log1` in `[2/3, 4/3]`, so its series ratio has magnitude at
most `1/3`. -/
def c5CenteredLogScale (m : ℕ) : ℕ :=
  if m ≤ 1 then 0 else if m ≤ 2 then 1 else if m ≤ 5 then 2 else
  if m ≤ 10 then 3 else if m ≤ 21 then 4 else if m ≤ 42 then 5 else
  if m ≤ 85 then 6 else 7

theorem c5CenteredLogScaleRange (m : ℕ) (hm0 : 1 ≤ m) (hm100 : m ≤ 100) :
    (2 / 3 : ℚ) ≤ (m : ℚ) / 2 ^ c5CenteredLogScale m ∧
      (m : ℚ) / 2 ^ c5CenteredLogScale m ≤ 4 / 3 := by
  interval_cases m <;> norm_num [c5CenteredLogScale]

theorem c5CenteredLogScaleLeSeven (m : ℕ) : c5CenteredLogScale m ≤ 7 := by
  unfold c5CenteredLogScale
  split_ifs <;> omega

private theorem c5_geom_third (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 3 : ℚ) ^ (i + 1)) =
      (1 - (1 / 3 : ℚ) ^ n) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [pow_succ]
      ring

private theorem c5_geom_half (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 2 : ℚ) ^ (i + 1)) =
      1 - (1 / 2 : ℚ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [pow_succ]
      ring

private theorem c5_abs_logSum_third {n : ℕ} {q : ℚ} (hq : |q| ≤ 1 / 3) :
    |Interval.logSum n q| ≤ 1 / 2 := by
  unfold Interval.logSum
  calc
    |∑ i ∈ Finset.range n, q ^ (i + 1) / (i + 1)| ≤
        ∑ i ∈ Finset.range n, |q ^ (i + 1) / (i + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, (1 / 3 : ℚ) ^ (i + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hden : (1 : ℚ) ≤ (i : ℚ) + 1 := by
        exact_mod_cast (show 1 ≤ i + 1 by omega)
      rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (i + 1 : ℚ))]
      calc
        |q| ^ (i + 1) / (i + 1 : ℚ) ≤ |q| ^ (i + 1) :=
          div_le_self (by positivity) hden
        _ ≤ (1 / 3 : ℚ) ^ (i + 1) :=
          pow_le_pow_left₀ (abs_nonneg q) hq (i + 1)
    _ = (1 - (1 / 3 : ℚ) ^ n) / 2 := c5_geom_third n
    _ ≤ 1 / 2 := by
      have hn : 0 ≤ (1 / 3 : ℚ) ^ n := pow_nonneg (by norm_num) _
      nlinarith

private theorem c5_abs_logSum_half {n : ℕ} {q : ℚ} (hq : |q| ≤ 1 / 2) :
    |Interval.logSum n q| ≤ 1 := by
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
      rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (i + 1 : ℚ))]
      calc
        |q| ^ (i + 1) / (i + 1 : ℚ) ≤ |q| ^ (i + 1) :=
          div_le_self (by positivity) hden
        _ ≤ (1 / 2 : ℚ) ^ (i + 1) :=
          pow_le_pow_left₀ (abs_nonneg q) hq (i + 1)
    _ = 1 - (1 / 2 : ℚ) ^ n := c5_geom_half n
    _ ≤ 1 := by
      have hn : 0 ≤ (1 / 2 : ℚ) ^ n := pow_nonneg (by norm_num) _
      linarith

private theorem c5_abs_logRem_third {n : ℕ} {q : ℚ} (hq : |q| ≤ 1 / 3) :
    |Interval.logRem n q| ≤ 1 / 2 := by
  unfold Interval.logRem
  have hden : 0 < 1 - |q| := by linarith [abs_nonneg q]
  have hpow : |q| ^ (n + 1) ≤ (1 / 3 : ℚ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg q) hq (n + 1)
  have hnum : |q| ^ (n + 1) ≤ 1 / 3 := by
    calc
      |q| ^ (n + 1) ≤ (1 / 3 : ℚ) ^ (n + 1) := hpow
      _ ≤ 1 / 3 := by
        have hpow' : (1 / 3 : ℚ) ^ n ≤ 1 := by
          exact pow_le_one₀
            (by norm_num : (0 : ℚ) ≤ (1 / 3 : ℚ))
            (by norm_num : (1 / 3 : ℚ) ≤ 1)
        rw [pow_succ]
        simpa using mul_le_mul_of_nonneg_right hpow'
          (by norm_num : (0 : ℚ) ≤ (1 / 3 : ℚ))
  rw [abs_of_nonneg (div_nonneg (pow_nonneg (abs_nonneg q) _) (le_of_lt hden))]
  rw [div_le_iff₀ hden]
  nlinarith [hq]

private theorem c5_abs_logRem_half {n : ℕ} {q : ℚ} (hq : |q| ≤ 1 / 2) :
    |Interval.logRem n q| ≤ 1 := by
  unfold Interval.logRem
  have hden : 0 < 1 - |q| := by linarith [abs_nonneg q]
  have hpow : |q| ^ (n + 1) ≤ (1 / 2 : ℚ) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg q) hq (n + 1)
  have hnum : |q| ^ (n + 1) ≤ 1 / 2 := by
    calc
      |q| ^ (n + 1) ≤ (1 / 2 : ℚ) ^ (n + 1) := hpow
      _ ≤ 1 / 2 := by
        have hpow' : (1 / 2 : ℚ) ^ n ≤ 1 := by
          exact pow_le_one₀
            (by norm_num : (0 : ℚ) ≤ (1 / 2 : ℚ))
            (by norm_num : (1 / 2 : ℚ) ≤ 1)
        rw [pow_succ]
        simpa using mul_le_mul_of_nonneg_right hpow'
          (by norm_num : (0 : ℚ) ≤ (1 / 2 : ℚ))
  rw [abs_of_nonneg (div_nonneg (pow_nonneg (abs_nonneg q) _) (le_of_lt hden))]
  rw [div_le_iff₀ hden]
  nlinarith [hq]

private theorem c5_abs_max_le {x y M : ℚ} (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |max x y| ≤ M := by
  apply abs_le.mpr
  constructor
  · exact (abs_le.mp hx).1.trans (le_max_left _ _)
  · exact max_le (abs_le.mp hx).2 (abs_le.mp hy).2

private theorem c5_log1_third_endpoint_bound (n : ℕ) (x : ℚ)
    (hq : |1 - x| ≤ 1 / 3) :
    |(Interval.log1 n (Interval.exact x)).lo| ≤ 1 ∧
      |(Interval.log1 n (Interval.exact x)).hi| ≤ 1 := by
  have hs := c5_abs_logSum_third (n := n) (q := 1 - x) hq
  have hr := c5_abs_logRem_third (n := n) (q := 1 - x) hq
  have hlo : |-(Interval.logSum n (1 - x)) - Interval.logRem n (1 - x)| ≤ 1 := by
    calc
      |-(Interval.logSum n (1 - x)) - Interval.logRem n (1 - x)| ≤
          |Interval.logSum n (1 - x)| + |Interval.logRem n (1 - x)| := by
            rw [show -Interval.logSum n (1 - x) - Interval.logRem n (1 - x) =
              -(Interval.logSum n (1 - x) + Interval.logRem n (1 - x)) by ring,
              abs_neg]
            exact abs_add_le (Interval.logSum n (1 - x))
              (Interval.logRem n (1 - x))
      _ ≤ 1 := by linarith
  have hhi0 : |-Interval.logSum n (1 - x) + Interval.logRem n (1 - x)| ≤ 1 := by
    calc
      |-Interval.logSum n (1 - x) + Interval.logRem n (1 - x)| ≤
          |Interval.logSum n (1 - x)| + |Interval.logRem n (1 - x)| := by
            simpa [abs_neg] using (abs_add_le (-Interval.logSum n (1 - x))
              (Interval.logRem n (1 - x)))
      _ ≤ 1 := by linarith
  constructor
  · simpa [Interval.log1, Interval.exact] using hlo
  · change |max (-Interval.logSum n (1 - x) + Interval.logRem n (1 - x))
      (-Interval.logSum n (1 - x) - Interval.logRem n (1 - x))| ≤ 1
    exact c5_abs_max_le hhi0 hlo

private theorem c5_log1_half_endpoint_bound (n : ℕ) :
    |(Interval.log1 n (Interval.exact (1 / 2))).lo| ≤ 2 ∧
      |(Interval.log1 n (Interval.exact (1 / 2))).hi| ≤ 2 := by
  have hq : |1 - (1 / 2 : ℚ)| ≤ 1 / 2 := by norm_num
  have hs := c5_abs_logSum_half (n := n) (q := 1 - (1 / 2 : ℚ)) hq
  have hr := c5_abs_logRem_half (n := n) (q := 1 - (1 / 2 : ℚ)) hq
  let S : ℚ := Interval.logSum n (1 - (1 / 2 : ℚ))
  let R : ℚ := Interval.logRem n (1 - (1 / 2 : ℚ))
  have hs' : |S| ≤ 1 := by simpa [S] using hs
  have hr' : |R| ≤ 1 := by simpa [R] using hr
  have hlo : |-S - R| ≤ 2 := by
    calc
      |-S - R| ≤ |S| + |R| := by
        rw [show -S - R = -(S + R) by ring, abs_neg]
        exact abs_add_le S R
      _ ≤ 2 := by linarith
  have hhi0 : |-S + R| ≤ 2 := by
    calc
      |-S + R| ≤ |S| + |R| := by
        simpa [abs_neg] using (abs_add_le (-S) R)
      _ ≤ 2 := by linarith
  constructor
  · simpa [Interval.log1, Interval.exact, S, R] using hlo
  · change |max (-S + R) (-S - R)| ≤ 2
    exact c5_abs_max_le hhi0 hlo

/-- A fast enclosure of `log 2`, using `log 2 = log(4/3) - log(2/3)`.
Both logarithm series have ratio at most `1/3`. -/
def c5CenteredLog2I (nLog : ℕ) : Interval :=
  (Interval.log1 nLog (Interval.exact (4 / 3))).add
    (Interval.log1 nLog (Interval.exact (2 / 3))).neg

theorem c5CenteredLog2IContains (nLog : ℕ) :
    (c5CenteredLog2I nLog).contains (Real.log 2) := by
  have hFour := Interval.contains_log1 (n := nLog)
    (Interval.contains_exact (4 / 3 : ℚ)) (by norm_num [Interval.exact])
    (by norm_num [Interval.exact])
  have hTwo := Interval.contains_log1 (n := nLog)
    (Interval.contains_exact (2 / 3 : ℚ)) (by norm_num [Interval.exact])
    (by norm_num [Interval.exact])
  have hsum : (c5CenteredLog2I nLog).contains
      (Real.log (4 / 3 : ℝ) + -Real.log (2 / 3 : ℝ)) := by
    simpa [c5CenteredLog2I] using Interval.contains_add hFour (Interval.contains_neg hTwo)
  have hiden : Real.log (4 / 3 : ℝ) + -Real.log (2 / 3 : ℝ) = Real.log 2 := by
    calc
      _ = Real.log (4 / 3 : ℝ) - Real.log (2 / 3 : ℝ) := by ring
      _ = Real.log ((4 / 3 : ℝ) / (2 / 3 : ℝ)) := by
        rw [← Real.log_div (by norm_num) (by norm_num)]
      _ = Real.log 2 := by congr 1; norm_num
  rw [hiden] at hsum
  exact hsum

theorem c5CenteredLog2IAbsBound (nLog : ℕ) :
    |(c5CenteredLog2I nLog).lo| ≤ 2 ∧ |(c5CenteredLog2I nLog).hi| ≤ 2 := by
  have hFour := c5_log1_third_endpoint_bound nLog (4 / 3 : ℚ) (by norm_num)
  have hTwo := c5_log1_third_endpoint_bound nLog (2 / 3 : ℚ) (by norm_num)
  constructor
  · change |(Interval.log1 nLog (Interval.exact (4 / 3))).lo +
      -(Interval.log1 nLog (Interval.exact (2 / 3))).hi| ≤ 2
    calc
      _ ≤ |(Interval.log1 nLog (Interval.exact (4 / 3))).lo| +
          |-(Interval.log1 nLog (Interval.exact (2 / 3))).hi| := abs_add_le _ _
      _ ≤ 2 := by simpa [abs_neg] using (by linarith [hFour.1, hTwo.2])
  · change |(Interval.log1 nLog (Interval.exact (4 / 3))).hi +
      -(Interval.log1 nLog (Interval.exact (2 / 3))).lo| ≤ 2
    calc
      _ ≤ |(Interval.log1 nLog (Interval.exact (4 / 3))).hi| +
          |-(Interval.log1 nLog (Interval.exact (2 / 3))).lo| := abs_add_le _ _
      _ ≤ 2 := by simpa [abs_neg] using (by linarith [hFour.2, hTwo.1])

/-! A rounded, linearly accumulated version of the rational logarithm
series.  The usual `Interval.logSum` recomputes each power independently;
this state carries the next power and rounds the partial sum after each term. -/
private theorem c5IntervalCoarsenLoError (p : ℕ) (x : Interval) :
    x.lo - 1 / (2 : ℚ) ^ p ≤ (x.coarsen p).lo := by
  have hD : (0 : ℚ) < (2 : ℚ) ^ p := by positivity
  have hfloor : x.lo * (2 : ℚ) ^ p - 1 <
      (Int.floor (x.lo * (2 : ℚ) ^ p) : ℚ) := by
    have h := Int.lt_floor_add_one (x.lo * (2 : ℚ) ^ p)
    linarith
  have hscaled :
      (x.lo - 1 / (2 : ℚ) ^ p) * (2 : ℚ) ^ p ≤
        (Int.floor (x.lo * (2 : ℚ) ^ p) : ℚ) := by
    rw [sub_mul, div_mul_cancel₀ _ hD.ne']
    exact le_of_lt hfloor
  change x.lo - 1 / (2 : ℚ) ^ p ≤
    (Int.floor (x.lo * (2 : ℚ) ^ p) : ℚ) / (2 : ℚ) ^ p
  exact (le_div_iff₀ hD).2 hscaled

private theorem c5IntervalCoarsenHiError (p : ℕ) (x : Interval) :
    (x.coarsen p).hi ≤ x.hi + 1 / (2 : ℚ) ^ p := by
  have hD : (0 : ℚ) < (2 : ℚ) ^ p := by positivity
  have hceil : (Int.ceil (x.hi * (2 : ℚ) ^ p) : ℚ) <
      x.hi * (2 : ℚ) ^ p + 1 := by
    have h := Int.ceil_lt_add_one (x.hi * (2 : ℚ) ^ p)
    linarith
  have hscaled :
      (Int.ceil (x.hi * (2 : ℚ) ^ p) : ℚ) ≤
        (x.hi + 1 / (2 : ℚ) ^ p) * (2 : ℚ) ^ p := by
    rw [add_mul, div_mul_cancel₀ _ hD.ne']
    exact le_of_lt hceil
  change (Int.ceil (x.hi * (2 : ℚ) ^ p) : ℚ) / (2 : ℚ) ^ p ≤
    x.hi + 1 / (2 : ℚ) ^ p
  exact (div_le_iff₀ hD).2 hscaled

def c5CenteredFastLogSumState (p : ℕ) (q : ℚ) : ℕ → ℚ × Interval
  | 0 => (q, Interval.exact 0)
  | n + 1 =>
      let prev := c5CenteredFastLogSumState p q n
      (prev.1 * q,
        (prev.2.add (Interval.exact (prev.1 / ((n + 1 : ℕ) : ℚ)))).coarsen p)

private theorem c5CenteredFastLogSumState_pow (p : ℕ) (q : ℚ) :
    ∀ n, (c5CenteredFastLogSumState p q n).1 = q ^ (n + 1)
  | 0 => by simp [c5CenteredFastLogSumState]
  | n + 1 => by
      change (c5CenteredFastLogSumState p q n).1 * q = q ^ (n + 1 + 1)
      rw [c5CenteredFastLogSumState_pow p q n]
      exact (pow_succ q (n + 1)).symm

private theorem c5CenteredLogSumSucc (n : ℕ) (q : ℚ) :
    Interval.logSum (n + 1) q =
      Interval.logSum n q + q ^ (n + 1) / ((n + 1 : ℕ) : ℚ) := by
  unfold Interval.logSum
  rw [Finset.sum_range_succ, Nat.cast_succ]

private theorem c5CenteredFastLogSumState_contains (p : ℕ) (q : ℚ) :
    ∀ n, (c5CenteredFastLogSumState p q n).2.contains
      (Interval.logSum n q : ℝ)
  | 0 => by
      simp [c5CenteredFastLogSumState, Interval.logSum, Interval.contains,
        Interval.exact]
  | n + 1 => by
      have ih := c5CenteredFastLogSumState_contains p q n
      have hpow := c5CenteredFastLogSumState_pow p q n
      have hcast :
          ((q ^ (n + 1) / ((n + 1 : ℕ) : ℚ) : ℚ) : ℝ) =
            (q : ℝ) ^ (n + 1) / (n + 1 : ℝ) := by
        push_cast
        rfl
      have hterm :
          (Interval.exact ((c5CenteredFastLogSumState p q n).1 /
            ((n + 1 : ℕ) : ℚ))).contains
              ((q : ℝ) ^ (n + 1) / (n + 1 : ℝ)) := by
        rw [hpow, ← hcast]
        exact Interval.contains_exact _
      have hsum := Interval.contains_coarsen p
        (Interval.contains_add ih hterm)
      have hsumCast : (Interval.logSum (n + 1) q : ℝ) =
          (Interval.logSum n q : ℝ) +
            (q : ℝ) ^ (n + 1) / (n + 1 : ℝ) := by
        rw [c5CenteredLogSumSucc]
        push_cast
        rfl
      rw [← hsumCast] at hsum
      exact hsum

private theorem c5CenteredFastLogSumState_bounds (p : ℕ) (q : ℚ) :
    ∀ n,
      Interval.logSum n q - (n : ℚ) / (2 : ℚ) ^ p ≤
          (c5CenteredFastLogSumState p q n).2.lo ∧
        (c5CenteredFastLogSumState p q n).2.hi ≤
          Interval.logSum n q + (n : ℚ) / (2 : ℚ) ^ p
  | 0 => by simp [c5CenteredFastLogSumState, Interval.logSum, Interval.exact]
  | n + 1 => by
      have ih := c5CenteredFastLogSumState_bounds p q n
      have hpow := c5CenteredFastLogSumState_pow p q n
      have hlog := c5CenteredLogSumSucc n q
      have hdelta : ((n + 1 : ℕ) : ℚ) / (2 : ℚ) ^ p =
          (n : ℚ) / (2 : ℚ) ^ p + 1 / (2 : ℚ) ^ p := by
        rw [Nat.cast_succ]
        ring
      have hroundLo := c5IntervalCoarsenLoError p
        ((c5CenteredFastLogSumState p q n).2.add
          (Interval.exact ((c5CenteredFastLogSumState p q n).1 /
            ((n + 1 : ℕ) : ℚ))))
      have hroundHi := c5IntervalCoarsenHiError p
        ((c5CenteredFastLogSumState p q n).2.add
          (Interval.exact ((c5CenteredFastLogSumState p q n).1 /
            ((n + 1 : ℕ) : ℚ))))
      have hroundLo' :
          (c5CenteredFastLogSumState p q n).2.lo +
              (c5CenteredFastLogSumState p q n).1 / ((n + 1 : ℕ) : ℚ) -
                1 / (2 : ℚ) ^ p ≤
            (((c5CenteredFastLogSumState p q n).2.add
              (Interval.exact ((c5CenteredFastLogSumState p q n).1 /
                ((n + 1 : ℕ) : ℚ)))).coarsen p).lo := by
        simpa [Interval.add, Interval.exact] using hroundLo
      have hroundHi' :
          (((c5CenteredFastLogSumState p q n).2.add
            (Interval.exact ((c5CenteredFastLogSumState p q n).1 /
              ((n + 1 : ℕ) : ℚ)))).coarsen p).hi ≤
            (c5CenteredFastLogSumState p q n).2.hi +
              (c5CenteredFastLogSumState p q n).1 / ((n + 1 : ℕ) : ℚ) +
                1 / (2 : ℚ) ^ p := by
        simpa [Interval.add, Interval.exact] using hroundHi
      rw [hpow] at hroundLo' hroundHi'
      change
        Interval.logSum (n + 1) q - ((n + 1 : ℕ) : ℚ) / (2 : ℚ) ^ p ≤
            (((c5CenteredFastLogSumState p q n).2.add
              (Interval.exact ((c5CenteredFastLogSumState p q n).1 /
                ((n + 1 : ℕ) : ℚ)))).coarsen p).lo ∧
          (((c5CenteredFastLogSumState p q n).2.add
            (Interval.exact ((c5CenteredFastLogSumState p q n).1 /
              ((n + 1 : ℕ) : ℚ)))).coarsen p).hi ≤
            Interval.logSum (n + 1) q + ((n + 1 : ℕ) : ℚ) / (2 : ℚ) ^ p
      constructor
      · rw [hlog, hdelta]
        rw [hpow]
        push_cast at *
        linarith [ih.1, hroundLo']
      · rw [hlog, hdelta]
        rw [hpow]
        push_cast at *
        linarith [ih.2, hroundHi']

private theorem c5NatLeTwoPow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      rw [pow_succ]
      omega

private theorem c5CenteredFastLogSumErrorLeOne (n : ℕ) :
    (n : ℚ) / (2 : ℚ) ^ (n + 384) ≤ 1 := by
  have hn : (n : ℚ) ≤ (2 : ℚ) ^ n := by exact_mod_cast c5NatLeTwoPow n
  have h384 : (1 : ℚ) ≤ (2 : ℚ) ^ 384 := by
    exact one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)
  have hpow : (2 : ℚ) ^ n ≤ (2 : ℚ) ^ (n + 384) := by
    rw [pow_add]
    simpa using mul_le_mul_of_nonneg_left h384
      (pow_nonneg (show (0 : ℚ) ≤ 2 by norm_num) n)
  have hnum : (n : ℚ) ≤ (2 : ℚ) ^ (n + 384) := hn.trans hpow
  exact (div_le_iff₀ (by positivity)).2 (by simpa using hnum)

private theorem c5CenteredIntervalEndpointAbsBound {S : Interval} {v ε : ℚ}
    (hvalue : |v| ≤ 1 / 2) (herr : ε ≤ 1)
    (hbelow : S.lo ≤ v) (habove : v ≤ S.hi)
    (hloErr : v - ε ≤ S.lo) (hhiErr : S.hi ≤ v + ε) :
    |S.lo| ≤ 3 / 2 ∧ |S.hi| ≤ 3 / 2 := by
  constructor
  · apply abs_le.mpr
    constructor <;> linarith [abs_le.mp hvalue]
  · apply abs_le.mpr
    constructor <;> linarith [abs_le.mp hvalue]

private theorem c5CenteredFastLogSumAbsBound (n : ℕ) (q : ℚ)
    (hq : |q| ≤ 1 / 3) :
    |(c5CenteredFastLogSumState (n + 384) q n).2.lo| ≤ 3 / 2 ∧
      |(c5CenteredFastLogSumState (n + 384) q n).2.hi| ≤ 3 / 2 := by
  have hsum := c5_abs_logSum_third (n := n) hq
  have hstate := c5CenteredFastLogSumState_contains (n + 384) q n
  have hlo : (c5CenteredFastLogSumState (n + 384) q n).2.lo ≤
      Interval.logSum n q := by exact_mod_cast hstate.1
  have hhi : Interval.logSum n q ≤
      (c5CenteredFastLogSumState (n + 384) q n).2.hi := by exact_mod_cast hstate.2
  have herr := c5CenteredFastLogSumState_bounds (n + 384) q n
  let ε : ℚ := (n : ℚ) / (2 : ℚ) ^ (n + 384)
  have herr' : ε ≤ 1 := by simpa [ε] using c5CenteredFastLogSumErrorLeOne n
  have hloErr : Interval.logSum n q - ε ≤
      (c5CenteredFastLogSumState (n + 384) q n).2.lo := by
    simpa [ε] using herr.1
  have hhiErr : (c5CenteredFastLogSumState (n + 384) q n).2.hi ≤
      Interval.logSum n q + ε := by
    simpa [ε] using herr.2
  exact c5CenteredIntervalEndpointAbsBound hsum herr'
    (by exact_mod_cast (c5CenteredFastLogSumState_contains (n + 384) q n).1)
    (by exact_mod_cast (c5CenteredFastLogSumState_contains (n + 384) q n).2)
    hloErr hhiErr

private def c5CenteredFastLog1Lower (n : ℕ) (x : Interval) : ℚ :=
  -((c5CenteredFastLogSumState (n + 384) (1 - x.lo) n).2.hi) -
    Interval.logRem n (1 - x.lo)

private def c5CenteredFastLog1Upper (n : ℕ) (x : Interval) : ℚ :=
  max
    (-((c5CenteredFastLogSumState (n + 384) (1 - x.hi) n).2.lo) +
      Interval.logRem n (1 - x.hi))
    (-((c5CenteredFastLogSumState (n + 384) (1 - x.lo) n).2.lo) -
      Interval.logRem n (1 - x.lo))

private theorem c5CenteredFastLog1Lower_le_log1 (n : ℕ) (x : Interval) :
    c5CenteredFastLog1Lower n x ≤ (Interval.log1 n x).lo := by
  have hs := c5CenteredFastLogSumState_contains (n + 384) (1 - x.lo) n
  have hsum : Interval.logSum n (1 - x.lo) ≤
      (c5CenteredFastLogSumState (n + 384) (1 - x.lo) n).2.hi := by
    exact_mod_cast hs.2
  dsimp [c5CenteredFastLog1Lower, Interval.log1]
  linarith

private theorem c5CenteredFastLog1Upper_ge_log1 (n : ℕ) (x : Interval) :
    (Interval.log1 n x).hi ≤ c5CenteredFastLog1Upper n x := by
  have hhi := c5CenteredFastLogSumState_contains (n + 384) (1 - x.hi) n
  have hlo := c5CenteredFastLogSumState_contains (n + 384) (1 - x.lo) n
  have hhi' :
      (c5CenteredFastLogSumState (n + 384) (1 - x.hi) n).2.lo ≤
        Interval.logSum n (1 - x.hi) := by exact_mod_cast hhi.1
  have hlo' :
      (c5CenteredFastLogSumState (n + 384) (1 - x.lo) n).2.lo ≤
        Interval.logSum n (1 - x.lo) := by exact_mod_cast hlo.1
  dsimp [c5CenteredFastLog1Upper, Interval.log1]
  exact max_le
    (le_trans (by linarith) (le_max_left _ _))
    (le_trans (by linarith) (le_max_right _ _))

def c5CenteredFastLog1 (n : ℕ) (x : Interval) : Interval :=
  { lo := c5CenteredFastLog1Lower n x,
    hi := c5CenteredFastLog1Upper n x,
    le := (c5CenteredFastLog1Lower_le_log1 n x).trans
      ((Interval.log1 n x).le.trans (c5CenteredFastLog1Upper_ge_log1 n x)) }

private theorem c5CenteredFastLog1Contains (n : ℕ) (x : Interval) (t : ℝ)
    (hx : x.contains t) (hlo : 0 < x.lo) (hhi : x.hi < 2) :
    (c5CenteredFastLog1 n x).contains (Real.log t) := by
  have hs := Interval.contains_log1 (n := n) hx hlo hhi
  refine ⟨?_, ?_⟩
  · have hcover := c5CenteredFastLog1Lower_le_log1 n x
    exact le_trans (by exact_mod_cast hcover) hs.1
  · have hcover := c5CenteredFastLog1Upper_ge_log1 n x
    exact le_trans hs.2 (by exact_mod_cast hcover)

private theorem c5CenteredFastLog1AbsBound (n : ℕ) (x : ℚ)
    (hq : |1 - x| ≤ 1 / 3) :
    |(c5CenteredFastLog1 n (Interval.exact x)).lo| ≤ 2 ∧
      |(c5CenteredFastLog1 n (Interval.exact x)).hi| ≤ 2 := by
  have hsum := c5CenteredFastLogSumAbsBound n (1 - x) hq
  have hrem := c5_abs_logRem_third (n := n) hq
  let S := (c5CenteredFastLogSumState (n + 384) (1 - x) n).2
  let R := Interval.logRem n (1 - x)
  have hlow : |-S.hi - R| ≤ 2 := by
    calc
      _ = |-(S.hi + R)| := by congr 1; ring
      _ = |S.hi + R| := abs_neg _
      _ ≤ |S.hi| + |R| := abs_add_le _ _
      _ ≤ 3 / 2 + 1 / 2 := add_le_add hsum.2 hrem
      _ = 2 := by norm_num
  have hUpperLeft : |-S.lo + R| ≤ 2 := by
    calc
      _ ≤ |-S.lo| + |R| := abs_add_le _ _
      _ = |S.lo| + |R| := by rw [abs_neg]
      _ ≤ 3 / 2 + 1 / 2 := add_le_add hsum.1 hrem
      _ = 2 := by norm_num
  have hUpperRight : |-S.lo - R| ≤ 2 := by
    calc
      _ = |-(S.lo + R)| := by congr 1; ring
      _ = |S.lo + R| := abs_neg _
      _ ≤ |S.lo| + |R| := abs_add_le _ _
      _ ≤ 3 / 2 + 1 / 2 := add_le_add hsum.1 hrem
      _ = 2 := by norm_num
  have hUpper := c5_abs_max_le hUpperLeft hUpperRight
  constructor
  · simpa [S, R, c5CenteredFastLog1, c5CenteredFastLog1Lower,
      c5CenteredFastLog1Upper, Interval.exact] using hlow
  · simpa [S, R, c5CenteredFastLog1, c5CenteredFastLog1Lower,
      c5CenteredFastLog1Upper, Interval.exact] using hUpper

def c5CenteredLogQFromLogTwo (nLog k : ℕ) (q : ℚ) (logTwo : Interval) : Interval :=
  ((Interval.exact (k : ℚ)).mul logTwo).add
    (c5CenteredFastLog1 nLog (Interval.exact (q / 2 ^ k)))

def c5CenteredLogQ (nLog k : ℕ) (q : ℚ) : Interval :=
  c5CenteredLogQFromLogTwo nLog k q (c5CenteredLog2I nLog)

theorem contains_c5CenteredLogQFromLogTwo {nLog k : ℕ} {q : ℚ}
    {logTwo : Interval} (hlogTwo : logTwo.contains (Real.log 2))
    (h0 : 0 < q / 2 ^ k) (h2 : q / 2 ^ k < 2) :
    (c5CenteredLogQFromLogTwo nLog k q logTwo).contains (Real.log q) := by
  have h2k : (0 : ℚ) < 2 ^ k := by positivity
  have hq0 : (0 : ℚ) < q := by
    have h := mul_pos h0 h2k
    rwa [div_mul_cancel₀ _ h2k.ne'] at h
  have hid : Real.log q = (k : ℝ) * Real.log 2 + Real.log ((q : ℝ) / 2 ^ k) := by
    rw [Real.log_div (by exact_mod_cast hq0.ne') (by positivity), Real.log_pow]
    ring
  have hA := Interval.contains_mul (Interval.contains_exact (k : ℚ)) hlogTwo
  have hB' : (c5CenteredFastLog1 nLog (Interval.exact (q / 2 ^ k))).contains
      (Real.log ((q / 2 ^ k : ℚ) : ℝ)) := by
    apply c5CenteredFastLog1Contains nLog (Interval.exact (q / 2 ^ k)) _
      (Interval.contains_exact _) (by exact_mod_cast h0) (by exact_mod_cast h2)
  have hC := Interval.contains_add hA hB'
  have hcast : ((q / 2 ^ k : ℚ) : ℝ) = (q : ℝ) / 2 ^ k := by
    push_cast
    ring
  rw [hcast] at hC
  rw [c5CenteredLogQFromLogTwo, hid,
    show (k : ℝ) = (((k : ℚ) : ℝ)) by push_cast; rfl]
  exact hC

theorem contains_c5CenteredLogQ {nLog k : ℕ} {q : ℚ}
    (h0 : 0 < q / 2 ^ k) (h2 : q / 2 ^ k < 2) :
    (c5CenteredLogQ nLog k q).contains (Real.log q) := by
  exact contains_c5CenteredLogQFromLogTwo (c5CenteredLog2IContains nLog) h0 h2

theorem c5CenteredLogQLogBound (nLog m : ℕ) (hm0 : 1 ≤ m) (hm100 : m ≤ 100) :
    |(c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).lo| ≤ 16 ∧
      |(c5CenteredLogQ nLog (c5CenteredLogScale m) (m : ℚ)).hi| ≤ 16 := by
  have hscale := c5CenteredLogScaleRange m hm0 hm100
  have hq : |1 - (m : ℚ) / 2 ^ c5CenteredLogScale m| ≤ 1 / 3 := by
    rcases hscale with ⟨hlo, hhi⟩
    rw [abs_le]
    constructor <;> linarith
  have hlog1 := c5CenteredFastLog1AbsBound nLog
    ((m : ℚ) / 2 ^ c5CenteredLogScale m) hq
  have hlog2 := c5CenteredLog2IAbsBound nLog
  have hk : 0 ≤ (c5CenteredLogScale m : ℚ) ∧
      |(c5CenteredLogScale m : ℚ)| ≤ 7 := by
    constructor
    · positivity
    · rw [abs_of_nonneg (by positivity)]
      exact_mod_cast c5CenteredLogScaleLeSeven m
  have hprod := c5AbsIntervalMulExactEndpoints
    (c := (c5CenteredLogScale m : ℚ)) (M := 2) hlog2.1 hlog2.2
  have hprod' :
      |((Interval.exact (c5CenteredLogScale m : ℚ)).mul
          (c5CenteredLog2I nLog)).lo| ≤ 14 ∧
        |((Interval.exact (c5CenteredLogScale m : ℚ)).mul
          (c5CenteredLog2I nLog)).hi| ≤ 14 := by
    constructor
    · calc
        _ ≤ |(c5CenteredLogScale m : ℚ)| * 2 := hprod.1
        _ ≤ 14 := by nlinarith [hk.2]
    · calc
        _ ≤ |(c5CenteredLogScale m : ℚ)| * 2 := hprod.2
        _ ≤ 14 := by nlinarith [hk.2]
  rw [c5CenteredLogQ, c5CenteredLogQFromLogTwo]
  simp only [Interval.add]
  constructor
  · calc
      _ ≤ |((Interval.exact (c5CenteredLogScale m : ℚ)).mul
          (c5CenteredLog2I nLog)).lo| +
          |(c5CenteredFastLog1 nLog (Interval.exact
            ((m : ℚ) / 2 ^ c5CenteredLogScale m))).lo| := abs_add_le _ _
      _ ≤ 16 := by linarith [hprod'.1, hlog1.1]
  · calc
      _ ≤ |((Interval.exact (c5CenteredLogScale m : ℚ)).mul
          (c5CenteredLog2I nLog)).hi| +
          |(c5CenteredFastLog1 nLog (Interval.exact
            ((m : ℚ) / 2 ^ c5CenteredLogScale m))).hi| := abs_add_le _ _
      _ ≤ 16 := by linarith [hprod'.2, hlog1.2]

theorem c5CenteredLogQAbsBound (nLog m : ℕ) (hm0 : 1 ≤ m) (hm100 : m ≤ 100) :
    |(Interval.logQ nLog (c5CenteredLogScale m) (m : ℚ)).lo| ≤ 15 ∧
      |(Interval.logQ nLog (c5CenteredLogScale m) (m : ℚ)).hi| ≤ 15 := by
  have hscale := c5CenteredLogScaleRange m hm0 hm100
  have hq : |1 - (m : ℚ) / 2 ^ c5CenteredLogScale m| ≤ 1 / 3 := by
    rcases hscale with ⟨hlo, hhi⟩
    rw [abs_le]
    constructor <;> linarith
  have hlog1 := c5_log1_third_endpoint_bound nLog
    ((m : ℚ) / 2 ^ c5CenteredLogScale m) hq
  have hlog2 := c5_log1_half_endpoint_bound nLog
  have hlog2' : |(Interval.log2I nLog).lo| ≤ 2 ∧
      |(Interval.log2I nLog).hi| ≤ 2 := by
    constructor
    · simpa [Interval.log2I, Interval.neg] using hlog2.2
    · simpa [Interval.log2I, Interval.neg] using hlog2.1
  have hk : 0 ≤ (c5CenteredLogScale m : ℚ) ∧
      |(c5CenteredLogScale m : ℚ)| ≤ 7 := by
    constructor
    · positivity
    · rw [abs_of_nonneg (by positivity)]
      exact_mod_cast c5CenteredLogScaleLeSeven m
  have hprod := c5AbsIntervalMulExactEndpoints
    (c := (c5CenteredLogScale m : ℚ)) (M := 2) hlog2'.1 hlog2'.2
  have hprod' :
      |((Interval.exact (c5CenteredLogScale m : ℚ)).mul (Interval.log2I nLog)).lo| ≤ 14 ∧
        |((Interval.exact (c5CenteredLogScale m : ℚ)).mul (Interval.log2I nLog)).hi| ≤ 14 := by
    constructor
    · calc
        _ ≤ |(c5CenteredLogScale m : ℚ)| * 2 := hprod.1
        _ ≤ 14 := by nlinarith [hk.2]
    · calc
        _ ≤ |(c5CenteredLogScale m : ℚ)| * 2 := hprod.2
        _ ≤ 14 := by nlinarith [hk.2]

  rw [Interval.logQ]
  simp only [Interval.add]
  constructor
  · calc
      _ ≤ |((Interval.exact (c5CenteredLogScale m : ℚ)).mul (Interval.log2I nLog)).lo| +
          |(Interval.log1 nLog (Interval.exact ((m : ℚ) / 2 ^ c5CenteredLogScale m))).lo| :=
        abs_add_le _ _
      _ ≤ 15 := by linarith [hprod'.1, hlog1.1]
  · calc
      _ ≤ |((Interval.exact (c5CenteredLogScale m : ℚ)).mul (Interval.log2I nLog)).hi| +
          |(Interval.log1 nLog (Interval.exact ((m : ℚ) / 2 ^ c5CenteredLogScale m))).hi| :=
        abs_add_le _ _
      _ ≤ 15 := by linarith [hprod'.2, hlog1.2]

end CarrySigmaObstruction
