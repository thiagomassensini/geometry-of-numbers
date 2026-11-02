/-
# Variational second σ-derivative of the Schur pivot (positivity-free)

For a `C²` self-adjoint operator family `L` (the completed Hankel `G_N(σ)` as an operator
on a real inner product space), a `C¹` vector family `v` (the Schur vector `criticalVector`),
a fixed `w` (`e_last`) and scalar `P` (the pivot `sourceMomentSchur`) satisfying the Schur
relation `L v = P • w` and the normalization `⟪w, v⟫ = 1`, the pivot is stationary and, at a
point where `L' = 0` (central parity), its second derivative is the Schur-vector sandwich of
the operator curvature:

    ∂²_σ P (t₀) = ⟪v t₀, (L'' t₀) (v t₀)⟫.

Only the Schur relation (prefix invertibility), self-adjointness (reality) and parity are
used — **no positivity**.  This is the calculus lift of `schurVector_curvature`.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

namespace MomentosHankel

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Variational second derivative of the Schur pivot (positivity-free).**  `L`
self-adjoint and `C²`, `v` `C¹`, Schur relation `L v = P • w`, normalization `⟪w, v⟫ = 1`,
and `L' = 0` at `t₀` (central parity) imply `∂²_σ P (t₀) = ⟪v t₀, (L'' t₀) (v t₀)⟫`. -/
theorem pivot_second_deriv
    (v v₁ : ℝ → E) (L L₁ L₂ : ℝ → (E →L[ℝ] E)) (w : E) (P : ℝ → ℝ) (t₀ : ℝ)
    (hv : ∀ t, HasDerivAt v (v₁ t) t)
    (hL : ∀ t, HasDerivAt L (L₁ t) t) (hL₁ : ∀ t, HasDerivAt L₁ (L₂ t) t)
    (hself : ∀ (t : ℝ) (x y : E), ⟪(L t) x, y⟫ = ⟪x, (L t) y⟫)
    (hrel : ∀ t, (L t) (v t) = P t • w)
    (hnorm : ∀ t, ⟪w, v t⟫ = 1)
    (hpar : L₁ t₀ = 0) :
    deriv (deriv P) t₀ = ⟪v t₀, (L₂ t₀) (v t₀)⟫ := by
  have hqP : ∀ t, ⟪v t, (L t) (v t)⟫ = P t := by
    intro t
    rw [hrel t, real_inner_smul_right, real_inner_comm, hnorm t, mul_one]
  have hwv₁ : ∀ t, ⟪w, v₁ t⟫ = 0 := by
    intro t
    have h1 : HasDerivAt (fun s => ⟪w, v s⟫) (⟪w, v₁ t⟫) t := by
      simpa using HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_const t w) (hv t)
    have h2 : HasDerivAt (fun s => ⟪w, v s⟫) 0 t := by
      have he : (fun s => ⟪w, v s⟫) = fun _ => (1 : ℝ) := funext hnorm
      rw [he]; exact hasDerivAt_const t 1
    exact h1.unique h2
  have hLvv₁ : ∀ t, ⟪v t, (L t) (v₁ t)⟫ = 0 := by
    intro t
    rw [← hself t (v t) (v₁ t), hrel t, real_inner_smul_left, hwv₁ t, mul_zero]
  have hv₁Lv : ∀ t, ⟪v₁ t, (L t) (v t)⟫ = 0 := by
    intro t
    rw [hrel t, real_inner_smul_right, real_inner_comm, hwv₁ t, mul_zero]
  have hq1 : ∀ t, HasDerivAt (fun s => ⟪v s, (L s) (v s)⟫) (⟪v t, (L₁ t) (v t)⟫) t := by
    intro t
    have hprod : HasDerivAt (fun s => (L s) (v s)) ((L₁ t) (v t) + (L t) (v₁ t)) t :=
      (hL t).clm_apply (hv t)
    have hinner := HasDerivAt.inner (𝕜 := ℝ) (hv t) hprod
    have heq : ⟪v t, (L₁ t) (v t) + (L t) (v₁ t)⟫ + ⟪v₁ t, (L t) (v t)⟫
        = ⟪v t, (L₁ t) (v t)⟫ := by
      rw [inner_add_right, hLvv₁ t, hv₁Lv t]; ring
    rwa [heq] at hinner
  have hq1deriv : deriv (fun s => ⟪v s, (L s) (v s)⟫) = fun t => ⟪v t, (L₁ t) (v t)⟫ :=
    funext (fun t => (hq1 t).deriv)
  have hq2 : HasDerivAt (fun s => ⟪v s, (L₁ s) (v s)⟫) (⟪v t₀, (L₂ t₀) (v t₀)⟫) t₀ := by
    have hprod : HasDerivAt (fun s => (L₁ s) (v s)) ((L₂ t₀) (v t₀) + (L₁ t₀) (v₁ t₀)) t₀ :=
      (hL₁ t₀).clm_apply (hv t₀)
    have hinner := HasDerivAt.inner (𝕜 := ℝ) (hv t₀) hprod
    have heq : ⟪v t₀, (L₂ t₀) (v t₀) + (L₁ t₀) (v₁ t₀)⟫ + ⟪v₁ t₀, (L₁ t₀) (v t₀)⟫
        = ⟪v t₀, (L₂ t₀) (v t₀)⟫ := by
      rw [hpar]; simp
    rwa [heq] at hinner
  have hPeq : P = fun t => ⟪v t, (L t) (v t)⟫ := funext (fun t => (hqP t).symm)
  rw [hPeq, hq1deriv]
  exact hq2.deriv

section Concrete
open Matrix
open scoped Matrix

/-- **Concrete instantiation to the completed Hankel.**  For a `C²` σ-family of symmetric
matrices `G` (the completed Hankel `G_N(σ)`, with derivatives `G₁, G₂` transported through
`Matrix.toEuclideanCLM`), a `C¹` Schur-vector family `v`, a fixed `w` (`e_last`) and pivot
`P` with the Schur relation `G v = P • w` and normalization `⟪w, v⟫ = 1`, central parity
`G₁ t₀ = 0` gives the pivot curvature as the Schur-vector sandwich of the matrix curvature:
`∂²_σ P (t₀) = v t₀ ⬝ᵥ G₂ t₀ *ᵥ v t₀`.  No positivity. -/
theorem pivot_second_deriv_matrix {n : ℕ}
    (G G₁ G₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v v₁ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (w : EuclideanSpace ℝ (Fin (n + 1)))
    (P : ℝ → ℝ) (t₀ : ℝ)
    (hv : ∀ t, HasDerivAt v (v₁ t) t)
    (hG : ∀ t, HasDerivAt (fun s => toEuclideanCLM (𝕜 := ℝ) (G s)) (toEuclideanCLM (𝕜 := ℝ) (G₁ t)) t)
    (hG₁ : ∀ t, HasDerivAt (fun s => toEuclideanCLM (𝕜 := ℝ) (G₁ s)) (toEuclideanCLM (𝕜 := ℝ) (G₂ t)) t)
    (hsym : ∀ t, (G t).IsSymm)
    (hrel : ∀ t, toEuclideanCLM (𝕜 := ℝ) (G t) (v t) = P t • w)
    (hnorm : ∀ t, ⟪w, v t⟫ = 1)
    (hpar : G₁ t₀ = 0) :
    deriv (deriv P) t₀ = v t₀ ⬝ᵥ G₂ t₀ *ᵥ v t₀ := by
  have key : deriv (deriv P) t₀ = ⟪v t₀, toEuclideanCLM (𝕜 := ℝ) (G₂ t₀) (v t₀)⟫ := by
    refine pivot_second_deriv v v₁ (fun t => toEuclideanCLM (𝕜 := ℝ) (G t))
      (fun t => toEuclideanCLM (𝕜 := ℝ) (G₁ t)) (fun t => toEuclideanCLM (𝕜 := ℝ) (G₂ t)) w P t₀
      hv hG hG₁ ?_ hrel hnorm ?_
    · intro t x y
      show ⟪toEuclideanCLM (𝕜 := ℝ) (G t) x, y⟫ = ⟪x, toEuclideanCLM (𝕜 := ℝ) (G t) y⟫
      rw [real_inner_comm, inner_toEuclideanCLM, inner_toEuclideanCLM, dotProduct_mulVec,
        ← mulVec_transpose, hsym t]
      exact dotProduct_comm _ _
    · show toEuclideanCLM (𝕜 := ℝ) (G₁ t₀) = 0
      simp only [hpar, map_zero]
  rw [key, inner_toEuclideanCLM]

end Concrete

end MomentosHankel
