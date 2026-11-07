import Mathlib.NumberTheory.Bernoulli

namespace CarrySigmaObstruction

open scoped BigOperators

/-- Build the Bernoulli-prime sequence once, retaining all earlier values in
an array so the recurrence can read them in constant time. -/
def c5BernoulliPrimeTable : ℕ → Array ℚ
  | 0 => #[]
  | n + 1 =>
      let prev := c5BernoulliPrimeTable n
      prev.push (1 - ∑ k ∈ Finset.range n,
        (n.choose k : ℚ) / ((n - k + 1 : ℕ) : ℚ) * prev.getD k 0)

theorem c5BernoulliPrimeTable_size (n : ℕ) :
    (c5BernoulliPrimeTable n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [c5BernoulliPrimeTable, ih]

theorem c5BernoulliPrimeTable_getD (n i : ℕ) (hi : i < n) :
    (c5BernoulliPrimeTable n).getD i 0 = bernoulli' i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      by_cases h : i < n
      · rw [c5BernoulliPrimeTable]
        have hs := c5BernoulliPrimeTable_size n
        have hget :
            ((c5BernoulliPrimeTable n).push
                (1 - ∑ k ∈ Finset.range n,
                  (n.choose k : ℚ) / ((n - k + 1 : ℕ) : ℚ) *
                    (c5BernoulliPrimeTable n).getD k 0)).getD i 0 =
              (c5BernoulliPrimeTable n).getD i 0 := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, hs]
          simp [Nat.ne_of_lt h]
        rw [hget]
        exact ih i h
      · have hieq : i = n := by omega
        subst i
        rw [c5BernoulliPrimeTable]
        have hs := c5BernoulliPrimeTable_size n
        have hget :
            ((c5BernoulliPrimeTable n).push
                (1 - ∑ k ∈ Finset.range n,
                  (n.choose k : ℚ) / ((n - k + 1 : ℕ) : ℚ) *
                    (c5BernoulliPrimeTable n).getD k 0)).getD n 0 =
              1 - ∑ k ∈ Finset.range n,
                (n.choose k : ℚ) / ((n - k + 1 : ℕ) : ℚ) *
                  (c5BernoulliPrimeTable n).getD k 0 := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, hs]
          simp
        rw [hget, bernoulli'_def]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        have hden : ((n - k + 1 : ℕ) : ℚ) =
            (n : ℚ) - (k : ℚ) + 1 := by
          rw [Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hklt)]
          norm_num
        rw [hden, ← ih k hklt]

end CarrySigmaObstruction
