import SigmaC5RationalNodePreciseLogBounds

namespace CarrySigmaObstruction

open ZetaLean ZetaLean.ComplexInterval
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Complex powers with outward rounding after each multiplication. -/
def c5RoundedPowI (p : ℕ) (x : ComplexInterval) : ℕ → ComplexInterval
  | 0 => ComplexInterval.exact 1 0
  | n + 1 => ((c5RoundedPowI p x n).mul x).coarsen p

theorem contains_c5RoundedPowI {p : ℕ} {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) : ∀ n, (c5RoundedPowI p x n).contains (z ^ n)
  | 0 => by
      rw [pow_zero]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        norm_num [c5RoundedPowI, ComplexInterval.exact,
          Interval.exact, Interval.contains]
  | n + 1 => by
      rw [pow_succ]
      exact ComplexInterval.contains_coarsen p
        (ComplexInterval.contains_mul (contains_c5RoundedPowI hx n) hx)

/-- Carry the current rounded power and the rounded Taylor sum together. This
computes every power once instead of rebuilding powers `0,…,n` from scratch at
each summand. -/
def c5RoundedExpStateC (p : ℕ) (x : ComplexInterval) :
    ℕ → ComplexInterval × ComplexInterval
  | 0 => (ComplexInterval.exact 1 0, ComplexInterval.exact 0 0)
  | n + 1 =>
      let prev := c5RoundedExpStateC p x n
      ((prev.1.mul x).coarsen p,
        (prev.2.add
          ((ComplexInterval.smulQ (1 / n.factorial) prev.1).coarsen p)).coarsen p)

theorem contains_c5RoundedExpStateC {p : ℕ} {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) : ∀ n,
      (c5RoundedExpStateC p x n).1.contains (z ^ n) ∧
        (c5RoundedExpStateC p x n).2.contains
          (∑ i ∈ Finset.range n, z ^ i / i.factorial)
  | 0 => by
      constructor
      · rw [pow_zero]
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
          norm_num [c5RoundedExpStateC, ComplexInterval.exact,
            Interval.exact, Interval.contains]
      · simpa [c5RoundedExpStateC] using ComplexInterval.contains_zero
  | n + 1 => by
      have ih := contains_c5RoundedExpStateC (p := p) hx n
      simp only [c5RoundedExpStateC, Finset.sum_range_succ]
      constructor
      · rw [pow_succ]
        exact ComplexInterval.contains_coarsen p
          (ComplexInterval.contains_mul ih.1 hx)
      · have hterm := ComplexInterval.contains_smulQ
          (q := 1 / n.factorial) ih.1
        rw [show ((((1 / n.factorial : ℚ) : ℝ)) : ℂ) * z ^ n =
            z ^ n / n.factorial by push_cast; ring] at hterm
        exact ComplexInterval.contains_coarsen p
          (ComplexInterval.contains_add ih.2
            (ComplexInterval.contains_coarsen p hterm))

/-- The Taylor sum with outward rounding after every term and addition. -/
def c5RoundedExpSumC (p : ℕ) (x : ComplexInterval) (n : ℕ) : ComplexInterval :=
  (c5RoundedExpStateC p x n).2

theorem contains_c5RoundedExpSumC {p : ℕ} {x : ComplexInterval} {z : ℂ}
    (hx : x.contains z) : ∀ n,
      (c5RoundedExpSumC p x n).contains
        (∑ i ∈ Finset.range n, z ^ i / i.factorial) := by
  intro n
  exact (contains_c5RoundedExpStateC (p := p) hx n).2

/-- Taylor remainder using the uniform `‖z‖≤1` bound, avoiding a large
power of the interval endpoint in the rational remainder. -/
def c5RoundedExpSmall (n p : ℕ) (x : ComplexInterval) : ComplexInterval :=
  (c5RoundedExpSumC p x n).inflate ((n + 1) / (n.factorial * n))

theorem contains_c5RoundedExpSmall {n p : ℕ} (hn : 0 < n)
    {x : ComplexInterval} {z : ℂ} (hx : x.contains z)
    (hb : normBound x ≤ 1) :
    (c5RoundedExpSmall n p x).contains (Complex.exp z) := by
  have hzBound := norm_le_normBound hx
  have hz1 : ‖z‖ ≤ 1 := hzBound.trans (by exact_mod_cast hb)
  have hexp := Complex.exp_bound hz1 hn
  have hpow : ‖z‖ ^ n ≤ 1 := by
    exact pow_le_one₀ (norm_nonneg z) hz1
  have hTaylor := contains_c5RoundedExpSumC (p := p) hx n
  have hfactor : (0 : ℝ) ≤ (n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹ := by
    positivity
  have hrem : ‖z‖ ^ n * ((n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹) ≤
      (((n + 1 : ℚ) / (n.factorial * n : ℚ) : ℚ) : ℝ) := by
    calc
      _ ≤ 1 * ((n.succ : ℝ) * ((n.factorial * n : ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_right hpow hfactor
      _ = (((n + 1 : ℚ) / (n.factorial * n : ℚ) : ℚ) : ℝ) := by
        push_cast [Nat.succ_eq_add_one]
        ring
  have hbound : ‖Complex.exp z -
      (∑ i ∈ Finset.range n, z ^ i / i.factorial)‖ ≤
        (((n + 1 : ℚ) / (n.factorial * n : ℚ) : ℚ) : ℝ) := hexp.trans hrem
  simpa [c5RoundedExpSmall] using ComplexInterval.contains_inflate hTaylor hbound

/-- `exp` on a complex box, rounding to `p` dyadic bits after every Taylor
power, Taylor addition and squaring. -/
def c5RoundedExpC (n p : ℕ) : ℕ → ComplexInterval → ComplexInterval
  | 0, x => c5RoundedExpSmall n p x
  | k + 1, x =>
      let y := c5RoundedExpC n p k (ComplexInterval.halveC x)
      (y.mul y).coarsen p

theorem contains_c5RoundedExpC (n p : ℕ) (hn : 0 < n) :
    ∀ (k : ℕ) (x : ComplexInterval) (z : ℂ), x.contains z →
      normBound x ≤ 2 ^ k → (c5RoundedExpC n p k x).contains (Complex.exp z)
  | 0, x, z, hx, hb => by
      exact contains_c5RoundedExpSmall hn hx (by simpa using hb)
  | k + 1, x, z, hx, hb => by
      have hy : (c5RoundedExpC n p k (ComplexInterval.halveC x)).contains
          (Complex.exp (z / 2)) := by
        refine contains_c5RoundedExpC n p hn k (ComplexInterval.halveC x)
          (z / 2) (ComplexInterval.contains_halveC hx) ?_
        rw [ComplexInterval.normBound_halveC]
        rw [pow_succ] at hb
        linarith
      have hmul := ComplexInterval.contains_mul hy hy
      rw [show Complex.exp (z / 2) * Complex.exp (z / 2) = Complex.exp z by
        rw [← Complex.exp_add]
        ring_nf] at hmul
      exact ComplexInterval.contains_coarsen p hmul

#print axioms contains_c5RoundedPowI
#print axioms contains_c5RoundedExpSumC
#print axioms contains_c5RoundedExpSmall
#print axioms contains_c5RoundedExpC

end CarrySigmaObstruction
