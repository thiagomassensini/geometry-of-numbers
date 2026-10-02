import GeometryOfNumbers.Analysis.PrimeResidualDepthCrosswalk
import GeometryOfNumbers.Analysis.AtlasEnergyPartition
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Prime voices of a quantity and their nonseed energy partition

Factorization is a downstream representation of the residual thresholds,
as proved in PrimeResidualDepthCrosswalk. Unique factorization gives a finite
logarithmic decomposition, whose normalization is a partition for quantities
`n > 1`. The unit sum is derived, not supplied as admissibility data.

Here `n` is a QUANTITY, not a camera radius/channel. No identification of these
indices or seed-plus-camera architecture has been proved. Consequently this
module does not instantiate AdmissibleAtlasPartition. At quantity one every
voice and weight is zero; total real division does not repair normalization.
The last theorem proves that the literal total family cannot instantiate the
current interface, irrespective of its proposed finite support.
-/

namespace GeometryOfNumbers.Analysis

open Geometry
open scoped BigOperators

noncomputable section

/-- A prime multiplicative voice of a quantity, represented logarithmically.
Nonprime labels vanish because their factorization coefficient is zero. -/
def primeCarryVoice (n p : Nat) : ℝ :=
  (n.factorization p : ℝ) * Real.log (p : ℝ)

theorem primeCarryVoice_eq_of_residual_thresholds {n p depth : Nat}
    (hp : Nat.Prime p) (hn : n ≠ 0)
    (h : ∀ k, HasCarryDepthAtLeast p n k ↔ k ≤ depth) :
    primeCarryVoice n p = (depth : ℝ) * Real.log (p : ℝ) := by
  rw [primeCarryVoice, (primeResidualDepth_factorization_characterized hp hn depth).2 h]

theorem primeCarryVoice_nonneg (n p : Nat) : 0 ≤ primeCarryVoice n p :=
  mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

theorem primeCarryVoice_off_support {n p : Nat} (hp : p ∉ n.factorization.support) :
    primeCarryVoice n p = 0 := by
  simp [primeCarryVoice, Finsupp.notMem_support_iff.mp hp]

theorem primeCarryVoice_nonprime {n p : Nat} (hp : ¬ Nat.Prime p) :
    primeCarryVoice n p = 0 := by
  simp [primeCarryVoice, Nat.factorization_eq_zero_of_not_prime n hp]

/-- Mathlib derives this identity by taking logarithms of the unique prime
product. Its total conventions also make the scalar equality true at zero;
the residual-depth representation still requires a nonzero quantity. -/
theorem log_eq_sum_primeCarryVoice (n : Nat) :
    Real.log (n : ℝ) = ∑ p ∈ n.factorization.support, primeCarryVoice n p := by
  simpa only [Finsupp.sum, primeCarryVoice] using Real.log_nat_eq_sum_factorization n

/-- Normalized voices. Admissibility is proved only for quantities greater
than one; a total definition must not be mistaken for a total partition. -/
def primeVoiceWeight (n p : Nat) : ℝ :=
  primeCarryVoice n p / Real.log (n : ℝ)

theorem primeVoiceWeight_nonneg (n p : Nat) : 0 ≤ primeVoiceWeight n p :=
  div_nonneg (primeCarryVoice_nonneg n p) (Real.log_natCast_nonneg n)

theorem primeVoiceWeight_off_support {n p : Nat} (hp : p ∉ n.factorization.support) :
    primeVoiceWeight n p = 0 := by
  rw [primeVoiceWeight, primeCarryVoice_off_support hp, zero_div]

theorem primeVoiceWeight_nonprime {n p : Nat} (hp : ¬ Nat.Prime p) :
    primeVoiceWeight n p = 0 := by
  rw [primeVoiceWeight, primeCarryVoice_nonprime hp, zero_div]

theorem primeVoiceWeight_support_finite (n : Nat) :
    (Function.support (primeVoiceWeight n)).Finite := by
  apply n.factorization.support.finite_toSet.subset
  intro p hp
  by_contra hnot
  exact hp (primeVoiceWeight_off_support hnot)

/-- The unit sum follows from unique factorization and positive log n. -/
theorem primeVoiceWeight_sum_eq_one {n : Nat} (hn : 1 < n) :
    ∑ p ∈ n.factorization.support, primeVoiceWeight n p = 1 := by
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  simp only [primeVoiceWeight, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← log_eq_sum_primeCarryVoice, mul_inv_cancel₀ hlog]

theorem primeVoiceWeight_finsum_eq_one {n : Nat} (hn : 1 < n) :
    (∑ᶠ p : Nat, primeVoiceWeight n p) = 1 := by
  rw [finsum_eq_sum_of_support_subset _ (s := n.factorization.support) (by
    intro p hp
    by_contra hnot
    exact hp (primeVoiceWeight_off_support hnot))]
  exact primeVoiceWeight_sum_eq_one hn

/-- A prime power has one voice of full weight; no fallback base is chosen. -/
theorem primeVoiceWeight_prime_pow {p k : Nat} (hp : Nat.Prime p) (hk : 0 < k) :
    primeVoiceWeight (p ^ k) p = 1 := by
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
  have hcast : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp only [primeVoiceWeight, primeCarryVoice, Nat.factorization_pow_self hp,
    Nat.cast_pow, Real.log_pow]
  exact div_self (mul_ne_zero hcast hlog)

theorem primeVoiceWeight_prime {p : Nat} (hp : Nat.Prime p) :
    primeVoiceWeight p p = 1 := by
  simpa using primeVoiceWeight_prime_pow hp (k := 1) Nat.zero_lt_one

theorem primeCarryVoice_one (p : Nat) : primeCarryVoice 1 p = 0 := by
  simp [primeCarryVoice]

theorem primeVoiceWeight_one (p : Nat) : primeVoiceWeight 1 p = 0 := by
  simp [primeVoiceWeight, primeCarryVoice_one]

theorem primeVoiceWeight_one_sum :
    (∑ p ∈ (1 : Nat).factorization.support, primeVoiceWeight 1 p) = 0 := by
  simp

theorem primeVoiceWeight_one_finsum : (∑ᶠ p : Nat, primeVoiceWeight 1 p) = 0 := by
  simp [primeVoiceWeight_one]

/-- Even after embedding prime labels among all natural bases, the literal
quantity-indexed family fails the interface's unit sum at one. This is not a
proof that a quantity-to-channel crosswalk exists. -/
theorem primeVoiceWeight_no_total_atlas_partition :
    ¬ ∃ P : AdmissibleAtlasPartition,
      ∀ (b : AtlasBase) (n : Nat), P.weight b n = primeVoiceWeight n b.val := by
  rintro ⟨P, h⟩
  have hunit := P.sum_eq_one 1
  simp only [h, primeVoiceWeight_one, Finset.sum_const_zero] at hunit
  exact zero_ne_one hunit

end

end GeometryOfNumbers.Analysis
