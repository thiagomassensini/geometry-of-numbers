/-
# Local-neighborhood transport of the moving-pivot curvature

This file transports the *moving* Schur-pivot curvature of `PivotSecondDerivative.lean`
to a neighborhood of the central abscissa, discharging the smoothness from a *local*
invertible prefix (the analytic input: the prefix determinant is analytic and nonzero at
the center, hence nonzero on an open `U ∋ t₀`).  The global `pivot_second_deriv_hankel`
needed invertibility/differentiability/`C²` for **all** `σ`; the actual completed-Hankel
family is invertible only near the center, so this local version is the faithful statement.

The moving critical direction `v(σ) = schurVector (A σ) (b σ)` varies with `σ`; central
parity (`G₁ t₀ = 0`) makes the first-order variation of the direction drop out, so the
second σ-derivative of the pivot coincides with the **fixed-vector** form
`schurVector (A t₀) (b t₀)ᵀ (∂²_σ G) schurVector (A t₀) (b t₀)` — the Schur-vector sandwich
`schurVector_curvature`.  No positivity is used.  This is the brick named in
`research/native-sixth-explicit-sigma/REPORT.md` §E of PR #139.
-/
import MomentosHankel.PivotSecondDerivative
import MomentosHankel.SchurPivotCurvature
import MomentosHankel.SchurVectorSmoothness

namespace MomentosHankel

open scoped RealInnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Local variational second derivative of the Schur pivot (positivity-free).**  Same
conclusion as `pivot_second_deriv`, but every structural hypothesis — differentiability of
`v` and `L`, self-adjointness, the Schur relation `L v = P • w` and the normalization
`⟪w, v⟫ = 1` — is only required on an open neighborhood `U ∋ t₀`; the second derivative of
`L` is needed at `t₀` alone.  Central parity `L₁ t₀ = 0` makes the moving-direction terms
cancel, giving `∂²_σ P (t₀) = ⟪v t₀, (L₂ t₀) (v t₀)⟫`. -/
theorem pivot_second_deriv_local
    (v v₁ : ℝ → E) (L L₁ L₂ : ℝ → (E →L[ℝ] E)) (w : E) (P : ℝ → ℝ) (t₀ : ℝ)
    (U : Set ℝ) (hU : IsOpen U) (ht₀ : t₀ ∈ U)
    (hv : ∀ t ∈ U, HasDerivAt v (v₁ t) t)
    (hL : ∀ t ∈ U, HasDerivAt L (L₁ t) t)
    (hL₁ : HasDerivAt L₁ (L₂ t₀) t₀)
    (hself : ∀ t ∈ U, ∀ x y : E, ⟪(L t) x, y⟫ = ⟪x, (L t) y⟫)
    (hrel : ∀ t ∈ U, (L t) (v t) = P t • w)
    (hnorm : ∀ t ∈ U, ⟪w, v t⟫ = 1)
    (hpar : L₁ t₀ = 0) :
    deriv (deriv P) t₀ = ⟪v t₀, (L₂ t₀) (v t₀)⟫ := by
  -- `⟪w, v₁⟫ = 0` on `U`: differentiate the locally constant `⟪w, v⟫ = 1`.
  have hwv₁ : ∀ t ∈ U, ⟪w, v₁ t⟫ = 0 := by
    intro t htU
    have h1 : HasDerivAt (fun s => ⟪w, v s⟫) (⟪w, v₁ t⟫) t := by
      simpa using HasDerivAt.inner (𝕜 := ℝ) (hasDerivAt_const t w) (hv t htU)
    have heq : (fun s => ⟪w, v s⟫) =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds htU) (fun s hs => hnorm s hs)
    have h2 : HasDerivAt (fun s => ⟪w, v s⟫) 0 t :=
      (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq
    exact h1.unique h2
  -- the two cross terms vanish on `U`
  have hLvv₁ : ∀ t ∈ U, ⟪v t, (L t) (v₁ t)⟫ = 0 := by
    intro t htU
    rw [← hself t htU (v t) (v₁ t), hrel t htU, real_inner_smul_left, hwv₁ t htU, mul_zero]
  have hv₁Lv : ∀ t ∈ U, ⟪v₁ t, (L t) (v t)⟫ = 0 := by
    intro t htU
    rw [hrel t htU, real_inner_smul_right, real_inner_comm, hwv₁ t htU, mul_zero]
  -- `P` is the quadratic form on `U`
  have hqP : ∀ t ∈ U, ⟪v t, (L t) (v t)⟫ = P t := by
    intro t htU
    rw [hrel t htU, real_inner_smul_right, real_inner_comm, hnorm t htU, mul_one]
  -- derivative of the quadratic form on `U`
  have hq1 : ∀ t ∈ U, HasDerivAt (fun s => ⟪v s, (L s) (v s)⟫) (⟪v t, (L₁ t) (v t)⟫) t := by
    intro t htU
    have hprod : HasDerivAt (fun s => (L s) (v s)) ((L₁ t) (v t) + (L t) (v₁ t)) t :=
      (hL t htU).clm_apply (hv t htU)
    have hinner := HasDerivAt.inner (𝕜 := ℝ) (hv t htU) hprod
    have heq : ⟪v t, (L₁ t) (v t) + (L t) (v₁ t)⟫ + ⟪v₁ t, (L t) (v t)⟫
        = ⟪v t, (L₁ t) (v t)⟫ := by
      rw [inner_add_right, hLvv₁ t htU, hv₁Lv t htU]; ring
    rwa [heq] at hinner
  -- `deriv P` agrees with `t ↦ ⟪v t, (L₁ t) (v t)⟫` near `t₀`
  have hderivP : deriv P =ᶠ[𝓝 t₀] (fun t => ⟪v t, (L₁ t) (v t)⟫) := by
    refine Filter.eventuallyEq_of_mem (hU.mem_nhds ht₀) (fun t htU => ?_)
    have hPeqU : P =ᶠ[𝓝 t] (fun s => ⟪v s, (L s) (v s)⟫) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds htU) (fun s hs => (hqP s hs).symm)
    exact ((hq1 t htU).congr_of_eventuallyEq hPeqU).deriv
  -- second derivative at `t₀`, parity killing the moving-direction term
  have hq2 : HasDerivAt (fun s => ⟪v s, (L₁ s) (v s)⟫) (⟪v t₀, (L₂ t₀) (v t₀)⟫) t₀ := by
    have hprod : HasDerivAt (fun s => (L₁ s) (v s)) ((L₂ t₀) (v t₀) + (L₁ t₀) (v₁ t₀)) t₀ :=
      hL₁.clm_apply (hv t₀ ht₀)
    have hinner := HasDerivAt.inner (𝕜 := ℝ) (hv t₀ ht₀) hprod
    have heq : ⟪v t₀, (L₂ t₀) (v t₀) + (L₁ t₀) (v₁ t₀)⟫ + ⟪v₁ t₀, (L₁ t₀) (v t₀)⟫
        = ⟪v t₀, (L₂ t₀) (v t₀)⟫ := by
      rw [hpar]; simp
    rwa [heq] at hinner
  rw [hderivP.deriv_eq]
  exact hq2.deriv

section Concrete
open Matrix
open scoped Matrix

/-- **Local concrete instantiation to the completed Hankel.**  Local analogue of
`pivot_second_deriv_matrix`: the `C²` σ-family of symmetric matrices, the `C¹` Schur vector,
self-adjointness and the Schur relation / normalization are required only on an open
`U ∋ t₀`; central parity `G₁ t₀ = 0` gives the pivot curvature as the Schur-vector sandwich
`∂²_σ P (t₀) = v t₀ ⬝ᵥ G₂ t₀ *ᵥ v t₀`.  Positivity-free. -/
theorem pivot_second_deriv_matrix_local {n : ℕ}
    (G G₁ G₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (v v₁ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (w : EuclideanSpace ℝ (Fin (n + 1)))
    (P : ℝ → ℝ) (t₀ : ℝ) (U : Set ℝ) (hU : IsOpen U) (ht₀ : t₀ ∈ U)
    (hv : ∀ t ∈ U, HasDerivAt v (v₁ t) t)
    (hG : ∀ t ∈ U, HasDerivAt (fun s => toEuclideanCLM (𝕜 := ℝ) (G s)) (toEuclideanCLM (𝕜 := ℝ) (G₁ t)) t)
    (hG₁ : HasDerivAt (fun s => toEuclideanCLM (𝕜 := ℝ) (G₁ s)) (toEuclideanCLM (𝕜 := ℝ) (G₂ t₀)) t₀)
    (hsym : ∀ t ∈ U, (G t).IsSymm)
    (hrel : ∀ t ∈ U, toEuclideanCLM (𝕜 := ℝ) (G t) (v t) = P t • w)
    (hnorm : ∀ t ∈ U, ⟪w, v t⟫ = 1)
    (hpar : G₁ t₀ = 0) :
    deriv (deriv P) t₀ = v t₀ ⬝ᵥ G₂ t₀ *ᵥ v t₀ := by
  have key : deriv (deriv P) t₀ = ⟪v t₀, toEuclideanCLM (𝕜 := ℝ) (G₂ t₀) (v t₀)⟫ := by
    refine pivot_second_deriv_local v v₁ (fun t => toEuclideanCLM (𝕜 := ℝ) (G t))
      (fun t => toEuclideanCLM (𝕜 := ℝ) (G₁ t)) (fun t => toEuclideanCLM (𝕜 := ℝ) (G₂ t)) w P t₀
      U hU ht₀ hv hG hG₁ ?_ hrel hnorm ?_
    · intro t htU x y
      show ⟪toEuclideanCLM (𝕜 := ℝ) (G t) x, y⟫ = ⟪x, toEuclideanCLM (𝕜 := ℝ) (G t) y⟫
      rw [real_inner_comm, inner_toEuclideanCLM, inner_toEuclideanCLM, dotProduct_mulVec,
        ← mulVec_transpose, hsym t htU]
      exact dotProduct_comm _ _
    · show toEuclideanCLM (𝕜 := ℝ) (G₁ t₀) = 0
      simp only [hpar, map_zero]
  rw [key, inner_toEuclideanCLM]

/-- **Local pivot curvature for the completed Hankel.**  For a σ-family `G` of symmetric
bordered-prefix matrices with a prefix invertible, differentiable and `C²` only on an open
`U ∋ t₀`, and central parity `G₁ t₀ = 0`, the second σ-derivative of the Schur pivot
`P = c - bᵀ A⁻¹ b` is the Schur-vector sandwich of the operator curvature `G₂`.  The block
hypotheses discharge `hrel`, `hnorm`, `hv`; positivity is never used. -/
theorem pivot_second_deriv_hankel_local {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → (Fin n → ℝ)) (c : ℝ → ℝ)
    (G G₁ G₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (t₀ : ℝ)
    (U : Set ℝ) (hU : IsOpen U) (ht₀ : t₀ ∈ U)
    (hGA : ∀ t i j, G t i.castSucc j.castSucc = A t i j)
    (hGb : ∀ t i, G t i.castSucc (Fin.last n) = b t i)
    (hGbt : ∀ t j, G t (Fin.last n) j.castSucc = b t j)
    (hGc : ∀ t, G t (Fin.last n) (Fin.last n) = c t)
    (hAinv : ∀ t ∈ U, IsUnit (A t))
    (hAd : ∀ t ∈ U, DifferentiableAt ℝ A t) (hbd : ∀ t ∈ U, DifferentiableAt ℝ b t)
    (hG : ∀ t ∈ U, HasDerivAt (fun s => toEuclideanCLM (𝕜 := ℝ) (G s)) (toEuclideanCLM (𝕜 := ℝ) (G₁ t)) t)
    (hG₁ : HasDerivAt (fun s => toEuclideanCLM (𝕜 := ℝ) (G₁ s)) (toEuclideanCLM (𝕜 := ℝ) (G₂ t₀)) t₀)
    (hsym : ∀ t ∈ U, (G t).IsSymm)
    (hpar : G₁ t₀ = 0) :
    deriv (deriv (fun t => c t - b t ⬝ᵥ ((A t)⁻¹ *ᵥ b t))) t₀
      = (WithLp.toLp 2 (schurVector (A t₀) (b t₀)) : EuclideanSpace ℝ (Fin (n + 1)))
          ⬝ᵥ G₂ t₀ *ᵥ WithLp.toLp 2 (schurVector (A t₀) (b t₀)) := by
  have hvdiff : ∀ t ∈ U, DifferentiableAt ℝ
      (fun s => (WithLp.toLp 2 (schurVector (A s) (b s)) : EuclideanSpace ℝ (Fin (n + 1)))) t := by
    intro t htU
    have hsv := schurVector_differentiableAt A b t (hAd t htU) (hAinv t htU) (hbd t htU)
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm.toContinuousLinearMap.differentiableAt).comp t hsv
  refine pivot_second_deriv_matrix_local G G₁ G₂
    (fun t => WithLp.toLp 2 (schurVector (A t) (b t)))
    (deriv (fun t => WithLp.toLp 2 (schurVector (A t) (b t))))
    (WithLp.toLp 2 (Pi.single (Fin.last n) 1))
    (fun t => c t - b t ⬝ᵥ ((A t)⁻¹ *ᵥ b t)) t₀
    U hU ht₀
    (fun t htU => (hvdiff t htU).hasDerivAt) hG hG₁ hsym ?_ ?_ hpar
  · intro t htU
    exact toEuclideanCLM_schurVector (A t) (b t) (c t) (G t)
      (hGA t) (hGb t) (hGbt t) (hGc t) (hAinv t htU)
  · intro t htU
    exact inner_eLast_schurVector (A t) (b t)

/-- **Local pivot curvature = fixed-vector polarized form.**  Composing the local Hankel
curvature with `schurVector_curvature`, the second σ-derivative of the moving pivot equals
the explicit fixed-vector expansion through the inverse prefix at the center.  This is the
Schur-complement value that `research/native-sixth-explicit-sigma/SigmaQuadratic.lean`
(`sigma_critical_form_curvature_center`) produces on the fixed central critical direction;
`hsym₂` is the (manifest) symmetry of the curvature matrix `∂²_σ G`. -/
theorem pivot_second_deriv_hankel_local_fixed_form {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ → (Fin n → ℝ)) (c : ℝ → ℝ)
    (G G₁ G₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (t₀ : ℝ)
    (U : Set ℝ) (hU : IsOpen U) (ht₀ : t₀ ∈ U)
    (hGA : ∀ t i j, G t i.castSucc j.castSucc = A t i j)
    (hGb : ∀ t i, G t i.castSucc (Fin.last n) = b t i)
    (hGbt : ∀ t j, G t (Fin.last n) j.castSucc = b t j)
    (hGc : ∀ t, G t (Fin.last n) (Fin.last n) = c t)
    (hAinv : ∀ t ∈ U, IsUnit (A t))
    (hAd : ∀ t ∈ U, DifferentiableAt ℝ A t) (hbd : ∀ t ∈ U, DifferentiableAt ℝ b t)
    (hG : ∀ t ∈ U, HasDerivAt (fun s => toEuclideanCLM (𝕜 := ℝ) (G s)) (toEuclideanCLM (𝕜 := ℝ) (G₁ t)) t)
    (hG₁ : HasDerivAt (fun s => toEuclideanCLM (𝕜 := ℝ) (G₁ s)) (toEuclideanCLM (𝕜 := ℝ) (G₂ t₀)) t₀)
    (hsym : ∀ t ∈ U, (G t).IsSymm)
    (hsym₂ : (G₂ t₀).IsSymm)
    (hpar : G₁ t₀ = 0) :
    deriv (deriv (fun t => c t - b t ⬝ᵥ ((A t)⁻¹ *ᵥ b t))) t₀
      = G₂ t₀ (Fin.last n) (Fin.last n)
        - 2 * ∑ k : Fin n, ((A t₀)⁻¹ *ᵥ b t₀) k * G₂ t₀ k.castSucc (Fin.last n)
        + ∑ i : Fin n, ((A t₀)⁻¹ *ᵥ b t₀) i
            * ∑ j : Fin n, G₂ t₀ i.castSucc j.castSucc * ((A t₀)⁻¹ *ᵥ b t₀) j := by
  rw [pivot_second_deriv_hankel_local A b c G G₁ G₂ t₀ U hU ht₀ hGA hGb hGbt hGc hAinv hAd hbd
    hG hG₁ hsym hpar]
  rw [show (WithLp.toLp 2 (schurVector (A t₀) (b t₀)) : EuclideanSpace ℝ (Fin (n + 1)))
        ⬝ᵥ G₂ t₀ *ᵥ WithLp.toLp 2 (schurVector (A t₀) (b t₀))
      = schurVector (A t₀) (b t₀) ⬝ᵥ (G₂ t₀ *ᵥ schurVector (A t₀) (b t₀)) from rfl]
  exact schurVector_curvature (A t₀) (b t₀) (G₂ t₀) hsym₂

end Concrete

end MomentosHankel
