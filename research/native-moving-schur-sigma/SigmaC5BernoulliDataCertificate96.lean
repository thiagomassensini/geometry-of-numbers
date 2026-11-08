import SigmaC5BernoulliDataCertificate64
import Mathlib.Tactic

namespace CarrySigmaObstruction

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem c5BernoulliPrimeTable_96_eq_data :
    c5BernoulliPrimeTable 96 = c5BernoulliPrimeDataPrefix96 := by
  have hvalue : ∀ n, n < 96 →
      bernoulli' n = c5BernoulliPrimeDataPrefix96.getD n 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        by_cases hn64 : n < 64
        · have hread := congrArg (fun a : Array ℚ => a.getD n 0)
            c5BernoulliPrimeTable_64_eq_data
          rw [c5BernoulliPrimeTable_getD 64 n hn64] at hread
          have hdata :
              c5BernoulliPrimeDataPrefix96.getD n 0 =
                c5BernoulliPrimeDataPrefix64.getD n 0 := by
            simp only [c5BernoulliPrimeDataPrefix96, Array.getD_eq_getD_getElem?]
            rw [Array.getElem?_append_left
              (by simpa [c5BernoulliPrimeDataPrefix64,
                c5BernoulliPrimeDataPrefix32] using hn64)]
          rw [← hdata] at hread
          exact hread
        · have hnlo : 64 ≤ n := by omega
          by_cases hodd : Odd n
          · rw [bernoulli'_eq_zero_of_odd hodd (by omega)]
            interval_cases n <;>
              norm_num [c5BernoulliPrimeDataPrefix96,
                c5BernoulliPrimeDataPrefix64,
                c5BernoulliPrimeDataPrefix32] at *
          · rw [bernoulli'_def]
            have hsum :
                (∑ k ∈ Finset.range n,
                  (n.choose k : ℚ) / ((n : ℚ) - k + 1) * bernoulli' k) =
                (∑ k ∈ Finset.range n,
                  (n.choose k : ℚ) / ((n : ℚ) - k + 1) *
                    c5BernoulliPrimeDataPrefix96.getD k 0) := by
              apply Finset.sum_congr rfl
              intro k hk
              congr 1
              have hklt : k < n := Finset.mem_range.mp hk
              exact ih k hklt (by omega)
            rw [hsum]
            interval_cases n <;>
              norm_num [c5BernoulliPrimeDataPrefix96,
                c5BernoulliPrimeDataPrefix64,
                c5BernoulliPrimeDataPrefix32, Finset.sum_range_succ, Nat.choose]
  apply Array.ext
  · simp [c5BernoulliPrimeTable_size, c5BernoulliPrimeDataPrefix96,
      c5BernoulliPrimeDataPrefix64, c5BernoulliPrimeDataPrefix32]
  · intro i hiTable hiData
    have hi : i < 96 := by simpa [c5BernoulliPrimeTable_size] using hiTable
    rw [Array.getElem_eq_getD (h := hiTable) (0 : ℚ),
      Array.getElem_eq_getD (h := hiData) (0 : ℚ)]
    rw [c5BernoulliPrimeTable_getD 96 i hi]
    exact hvalue i hi

#print axioms c5BernoulliPrimeTable_96_eq_data

end CarrySigmaObstruction
