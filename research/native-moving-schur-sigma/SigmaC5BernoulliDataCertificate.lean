import SigmaC5BernoulliDataTable
import Mathlib.Tactic

namespace CarrySigmaObstruction

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem c5BernoulliPrimeTable_32_eq_data :
    c5BernoulliPrimeTable 32 = c5BernoulliPrimeDataPrefix32 := by
  have hprefix : ∀ n, n ≤ 32 →
      c5BernoulliPrimeTable n = c5BernoulliPrimeDataPrefix32.extract 0 n := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [c5BernoulliPrimeTable, c5BernoulliPrimeDataPrefix32]
    | succ n ih =>
        intro hn
        rw [c5BernoulliPrimeTable]
        rw [ih (by omega)]
        have hn' : n ≤ 31 := by omega
        interval_cases n <;>
          norm_num [c5BernoulliPrimeDataPrefix32, Finset.sum_range_succ, Nat.choose]
  simpa [c5BernoulliPrimeDataPrefix32] using hprefix 32 le_rfl

#print axioms c5BernoulliPrimeTable_32_eq_data

end CarrySigmaObstruction
