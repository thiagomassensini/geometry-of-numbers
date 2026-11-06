import Mathlib.LinearAlgebra.Lagrange

/-!
# Exact rational interpolation for the finite C2 coefficient problem

This module establishes the algebraic interpolation identity used by the
129-node route.  It does not yet prove a numerical bound for the Lagrange
weights, a complex analytic bound for the source, or an inclusion in the
source coefficient boxes.
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
