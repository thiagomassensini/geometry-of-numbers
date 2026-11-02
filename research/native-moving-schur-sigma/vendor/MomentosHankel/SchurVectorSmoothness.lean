/-
# Differentiability of the Schur vector in σ (the analytic input for `hv`)

The one genuinely analytic hypothesis of `pivot_second_deriv_matrix` is the σ-smoothness of
the Schur vector `criticalVector = Fin.snoc (-(A⁻¹ *ᵥ b)) 1`, whose hard ingredient is the
differentiability of the matrix inverse `A(σ)⁻¹`.  Mathlib has no `fun_prop` automation for
matrix `det`/`adjugate`/`mulVec`/`inv`, so this is proven by hand: the inverse through the
normed-ring `differentiableAt_inverse` (`A⁻¹ = Ring.inverse A` by `nonsing_inv_eq_ringInverse`),
`mulVec` componentwise, and `Fin.snoc` by `Fin.lastCases`.

In `pivot_second_deriv` the derivative `v₁` of the Schur vector only enters terms that vanish
(stationarity + parity), so **differentiability alone** discharges `hv` (take `v₁ = deriv v`).
This file supplies that differentiability, positivity-free.
-/
import Mathlib

namespace MomentosHankel

open Matrix
open scoped Matrix

/-- The matrix inverse of a differentiable, pointwise-invertible family is differentiable.
Via `A⁻¹ = Ring.inverse A` and the normed-ring inverse derivative (L2 operator structure). -/
theorem matrixInverse_differentiableAt {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hA : DifferentiableAt ℝ A t) (hAu : IsUnit (A t)) :
    DifferentiableAt ℝ (fun s => (A s)⁻¹) t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℝ) := Matrix.instL2OpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.instL2OpNormedAlgebra
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  exact (differentiableAt_inverse hAu).comp t hA

/-- Matrix–vector product of differentiable families is differentiable (componentwise). -/
theorem mulVec_differentiableAt {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ → (Fin n → ℝ)) (t : ℝ) (hA : DifferentiableAt ℝ A t) (hb : DifferentiableAt ℝ b t) :
    DifferentiableAt ℝ (fun s => A s *ᵥ b s) t := by
  apply differentiableAt_pi.2
  intro i
  have e : (fun s => (A s *ᵥ b s) i) = (∑ j : Fin n, fun s => A s i j * b s j) := by
    funext s; simp [mulVec, dotProduct, Finset.sum_apply]
  rw [e]
  exact DifferentiableAt.sum fun j _ =>
    (differentiableAt_pi.mp (differentiableAt_pi.mp hA i) j).mul (differentiableAt_pi.mp hb j)

/-- **Differentiability of the Schur vector** `Fin.snoc (-(A⁻¹ *ᵥ b)) 1` in σ, from a
differentiable invertible prefix `A` and a differentiable coupling `b`.  This discharges the
smoothness hypothesis `hv` of `pivot_second_deriv_matrix` (take `v₁ = deriv v`), with no
positivity. -/
theorem schurVector_differentiableAt {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ → (Fin n → ℝ)) (t : ℝ)
    (hA : DifferentiableAt ℝ A t) (hAu : IsUnit (A t)) (hb : DifferentiableAt ℝ b t) :
    DifferentiableAt ℝ (fun s => (Fin.snoc (-((A s)⁻¹ *ᵥ b s)) (1 : ℝ) : Fin (n + 1) → ℝ)) t := by
  have hmul := mulVec_differentiableAt (fun s => (A s)⁻¹) b t
    (matrixInverse_differentiableAt A t hA hAu) hb
  apply differentiableAt_pi.2
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Fin.snoc_last]; exact differentiableAt_const _
  · intro k
    simp only [Fin.snoc_castSucc, Pi.neg_apply]
    exact (differentiableAt_pi.mp hmul k).neg

end MomentosHankel
