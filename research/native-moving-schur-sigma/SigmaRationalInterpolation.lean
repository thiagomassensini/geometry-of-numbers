import Mathlib.LinearAlgebra.Lagrange

/-!
# Exact rational interpolation for the finite C2 coefficient problem

This module establishes the algebraic interpolation identity used by the
129-node route.  It proves that the degree-zero scaled weight sum is exactly
one.  Bounds for the positive-degree weights, a complex analytic bound for the
source, and inclusion in the source coefficient boxes remain open.
-/

namespace CarrySigmaObstruction

open Finset Polynomial

noncomputable section

def c5InterpolationIndices : Finset ℕ := Finset.range 129

def c5InterpolationNode (j : ℕ) : ℚ := (j : ℚ) ^ 2

theorem c5InterpolationNode_injOn :
    Set.InjOn c5InterpolationNode (↑c5InterpolationIndices : Set ℕ) := by
  intro i _ j _ hij
  have hsq : i ^ 2 = j ^ 2 := by
    dsimp [c5InterpolationNode] at hij
    exact_mod_cast hij
  exact (Nat.pow_left_strictMono (by decide : 2 ≠ 0)).injective hsq

def c5LagrangeBasis (j : ℕ) : Polynomial ℚ :=
  Lagrange.basis c5InterpolationIndices c5InterpolationNode j

def c5InterpolationPolynomial (f : ℕ → ℚ) : Polynomial ℚ :=
  Lagrange.interpolate c5InterpolationIndices c5InterpolationNode f

def c5InterpolationWeight (j n : ℕ) : ℚ :=
  (100000 : ℚ) ^ (2 * n) * (c5LagrangeBasis j).coeff n

def c5InterpolationWeightSum (n : ℕ) : ℚ :=
  ∑ j ∈ c5InterpolationIndices, |c5InterpolationWeight j n|

theorem c5BasisDivisor_coeff_zero (x y : ℚ) :
    (Lagrange.basisDivisor x y).coeff 0 = -((x - y)⁻¹ * y) := by
  rw [Lagrange.basisDivisor, Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  simp

theorem c5LagrangeBasis_coeff_zero (j : ℕ) :
    (c5LagrangeBasis j).coeff 0 =
      ∏ k ∈ c5InterpolationIndices.erase j,
        -((c5InterpolationNode j - c5InterpolationNode k)⁻¹ *
          c5InterpolationNode k) := by
  simp [c5LagrangeBasis, Lagrange.basis, c5InterpolationIndices,
    Polynomial.coeff_zero_prod, c5BasisDivisor_coeff_zero]

theorem c5LagrangeBasis_coeff_zero_of_ne {j : ℕ} (hj : j ≠ 0) :
    (c5LagrangeBasis j).coeff 0 = 0 := by
  rw [c5LagrangeBasis_coeff_zero]
  refine Finset.prod_eq_zero (i := 0) ?_ ?_
  · exact Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_range.mpr (by norm_num)⟩
  · simp [c5InterpolationNode]

theorem c5LagrangeBasis_zero_coeff_zero :
    (c5LagrangeBasis 0).coeff 0 = 1 := by
  rw [c5LagrangeBasis_coeff_zero]
  apply Finset.prod_eq_one
  intro k hk
  have hkne : k ≠ 0 := (Finset.mem_erase.mp hk).1
  have hksq : ((k : ℚ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hkne)
  simp only [c5InterpolationNode, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0)]
  field_simp [hksq]
  ring

theorem c5InterpolationWeightSum_zero_eq_one :
    c5InterpolationWeightSum 0 = 1 := by
  rw [c5InterpolationWeightSum, ← Finset.sum_erase_add _ _
    (show 0 ∈ c5InterpolationIndices by simp [c5InterpolationIndices])]
  have hzero : c5InterpolationWeight 0 0 = 1 := by
    simp [c5InterpolationWeight, c5LagrangeBasis_zero_coeff_zero]
  have hrest : (∑ j ∈ c5InterpolationIndices.erase 0,
      |c5InterpolationWeight j 0|) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjne : j ≠ 0 := (Finset.mem_erase.mp hj).1
    simp [c5InterpolationWeight, c5LagrangeBasis_coeff_zero_of_ne hjne]
  rw [hrest, zero_add, hzero, abs_one]

theorem c5InterpolationPolynomial_coeff (f : ℕ → ℚ) (n : ℕ) :
    (c5InterpolationPolynomial f).coeff n =
      ∑ j ∈ c5InterpolationIndices,
        f j * (c5LagrangeBasis j).coeff n := by
  simp [c5InterpolationPolynomial, c5LagrangeBasis, Lagrange.interpolate_apply,
    Polynomial.coeff_C_mul]

theorem c5_interpolate_polynomial (p : Polynomial ℚ) (hp : p.degree < 129) :
    c5InterpolationPolynomial (fun j => p.eval (c5InterpolationNode j)) = p := by
  unfold c5InterpolationPolynomial
  symm
  apply Lagrange.eq_interpolate c5InterpolationNode_injOn
  simpa [c5InterpolationIndices] using hp

theorem c5InterpolationPolynomial_coeff_of_degree_lt
    (p : Polynomial ℚ) (hp : p.degree < 129) (n : ℕ) :
    p.coeff n =
      ∑ j ∈ c5InterpolationIndices,
        p.eval (c5InterpolationNode j) * (c5LagrangeBasis j).coeff n := by
  calc
    p.coeff n = (c5InterpolationPolynomial (fun j => p.eval (c5InterpolationNode j))).coeff n := by
      rw [c5_interpolate_polynomial p hp]
    _ = ∑ j ∈ c5InterpolationIndices,
          p.eval (c5InterpolationNode j) * (c5LagrangeBasis j).coeff n :=
      c5InterpolationPolynomial_coeff _ _

end
end CarrySigmaObstruction
