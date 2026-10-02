import GeometryOfNumbers.Geometry.ResidualTowerDepth
import Mathlib.Data.Nat.Factorization.Basic

assert_not_exists Real.log Real.exp

/-!
# Classical representation of the residual depth thresholds at prime bases

The residual tower and its depth relation already exist in Geometry. This
discrete crosswalk first uses their divisibility theorem, then the classical
prime factorization API. It defines no new depth and uses no real logarithm.
It lives in Analysis because Geometry's import policy excludes Mathlib.
The nonzero restriction preserves zero's unbounded residual-depth semantics.
-/

namespace GeometryOfNumbers.Analysis

open Geometry

theorem primeResidualDepth_iff_le_factorization {p n k : Nat}
    (hp : Nat.Prime p) (hn : n ≠ 0) :
    HasCarryDepthAtLeast p n k ↔ k ≤ n.factorization p :=
  (hasCarryDepthAtLeast_iff_dvd_pow p n k hp.pos).trans
    (hp.pow_dvd_iff_le_factorization hn)

/-- The entire threshold family characterizes the classical exponent; no
maximum-depth function is introduced. -/
theorem primeResidualDepth_factorization_characterized {p n : Nat}
    (hp : Nat.Prime p) (hn : n ≠ 0) (depth : Nat) :
    n.factorization p = depth ↔
      ∀ k, HasCarryDepthAtLeast p n k ↔ k ≤ depth := by
  constructor
  · intro h k
    rw [primeResidualDepth_iff_le_factorization hp hn, h]
  · intro h
    apply Nat.le_antisymm
    · exact (h _).1 ((primeResidualDepth_iff_le_factorization hp hn).2 (Nat.le_refl _))
    · exact (primeResidualDepth_iff_le_factorization hp hn).1 ((h _).2 (Nat.le_refl _))

theorem primeResidualDepth_one_iff {p k : Nat} (hp : Nat.Prime p) :
    HasCarryDepthAtLeast p 1 k ↔ k = 0 := by
  rw [primeResidualDepth_iff_le_factorization hp Nat.one_ne_zero]
  simp

/-- At zero the classical factorization convention cannot represent the
residual thresholds, even at level one. -/
theorem primeResidualDepth_zero_obstruction {p : Nat} (hp : Nat.Prime p) :
    HasCarryDepthAtLeast p 0 1 ∧ ¬ 1 ≤ (0 : Nat).factorization p :=
  ⟨hasCarryDepthAtLeast_zero_quantity p 1 hp.pos, by simp⟩

/-- Reconstruction uses the classical representation only downstream of the
threshold crosswalk. -/
theorem primeResidualDepth_reconstruction {n : Nat} (hn : n ≠ 0) :
    n.factorization.prod (fun p k => p ^ k) = n :=
  Nat.prod_factorization_pow_eq_self hn

/-- All prime residual threshold families together determine a nonzero
quantity. This does not assert a linear decomposition of composite cameras. -/
theorem primeResidualDepth_quantity_ext {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : ∀ p, Nat.Prime p → ∀ k,
      HasCarryDepthAtLeast p m k ↔ HasCarryDepthAtLeast p n k) : m = n := by
  apply Nat.eq_of_factorization_eq hm hn
  intro p
  by_cases hp : Nat.Prime p
  · apply Nat.le_antisymm
    · exact (primeResidualDepth_iff_le_factorization hp hn).1
        ((h p hp _).1 ((primeResidualDepth_iff_le_factorization hp hm).2 (Nat.le_refl _)))
    · exact (primeResidualDepth_iff_le_factorization hp hm).1
        ((h p hp _).2 ((primeResidualDepth_iff_le_factorization hp hn).2 (Nat.le_refl _)))
  · rw [Nat.factorization_eq_zero_of_not_prime m hp,
      Nat.factorization_eq_zero_of_not_prime n hp]

end GeometryOfNumbers.Analysis
