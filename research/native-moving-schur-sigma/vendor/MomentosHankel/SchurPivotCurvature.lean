/-
# Positivity-free curvature of the Schur pivot at the central abscissa

Let `G_N(σ)` be the completed native Hankel (entries `h_{i+j}(σ)`, `F = A·N`).  Its `N`-th
Schur pivot is `p_N = c - b^T A^{-1} b`, the complement of the prefix `A = G_{N-1}` in
`G_N`, with Schur vector `v₀ = (-A⁻¹ b ; 1)` (the `criticalVector` of the sibling
`tfvd-bezout-schur-residual` development).

Using ONLY the three ingredients — (i) invertibility of the prefix `A₀ = G_{N-1}(½)`
(so `v₀` exists), (ii) central parity `h_k(½+δ) = h_k(½-δ)` (so `G` is even in `δ`, hence
`∂_σ G(½) = 0` and the pivot is stationary), and (iii) the curvature recurrence
`∂²_σ h_k(½) = -2(k+1)(2k+3) h_{k+1}(½)` — the pivot's second σ-derivative is the Schur
vector sandwiching the curvature of `G`:

    ∂²_σ p_N(½) = v₀ᵀ (∂²_σ G_N(½)) v₀.

No positivity is assumed anywhere.  This file formalizes the positivity-free linear-algebra
core of that identity: the Schur-vector sandwich of ANY symmetric block `G'` expands with
the inverse prefix only (the explicit RHS below), and the pivot equals `v₀ᵀ G₀ v₀`.  The
stationarity `∂_σ p(½) = 0` is the `deriv_eq_zero_of_even_about` lemma of
`CompletedCharacteristicCurvature.lean`; the curvature entries are `sigma_curvature`; the
transport to the Bézout side is `sourceSchur_eq_scaled` (`p_B = c₀² p_H`).
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

namespace MomentosHankel

open Matrix
open scoped Matrix BigOperators RealInnerProductSpace

variable {n : ℕ}

/-- The Schur vector `v₀ = (-A⁻¹ b ; 1)` built from an invertible prefix `A` and the
coupling `b` (the `criticalVector` of the sibling repo). -/
noncomputable def schurVector (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (-(A⁻¹ *ᵥ b)) 1

/-- **Pivot as a sandwich (`p = v₀ᵀ G v₀`).**  Given the Schur relation
`G *ᵥ v₀ = Fin.snoc 0 p` (the content of `criticalVector_mulVec`), the sandwich of the
Schur vector recovers the pivot `p`.  Positivity-free: only the Schur relation is used. -/
theorem schurVector_pivot (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (p : ℝ)
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hrel : G *ᵥ schurVector A b = Fin.snoc 0 p) :
    schurVector A b ⬝ᵥ (G *ᵥ schurVector A b) = p := by
  rw [hrel, dotProduct, Fin.sum_univ_castSucc]
  simp [schurVector, Fin.snoc_castSucc, Fin.snoc_last]

/-- **Positivity-free Schur-vector curvature sandwich.**  For the Schur vector `v₀` of an
invertible prefix `A` and any symmetric block `G`, the sandwich `v₀ᵀ G v₀` expands through
the inverse prefix only:

    v₀ᵀ G v₀ = G(last,last) - 2 Σₖ (A⁻¹b)ₖ G(k,last) + Σᵢ Σⱼ (A⁻¹b)ᵢ (A⁻¹b)ⱼ G(i,j).

Specialized to `G = ∂²_σ G_N(½)` this is `∂²_σ p_N(½)` (the pivot curvature), and it uses no
positivity — only `A⁻¹` (prefix invertibility) and symmetry (from reality + parity). -/
theorem schurVector_curvature (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hG : G.IsSymm) :
    schurVector A b ⬝ᵥ (G *ᵥ schurVector A b)
      = G (Fin.last n) (Fin.last n)
        - 2 * ∑ k : Fin n, (A⁻¹ *ᵥ b) k * G k.castSucc (Fin.last n)
        + ∑ i : Fin n, (A⁻¹ *ᵥ b) i * ∑ j : Fin n, G i.castSucc j.castSucc * (A⁻¹ *ᵥ b) j := by
  have key : ∀ i : Fin (n + 1), (G *ᵥ schurVector A b) i
      = G i (Fin.last n) - ∑ j : Fin n, G i j.castSucc * (A⁻¹ *ᵥ b) j := by
    intro i
    simp only [schurVector, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last, Pi.neg_apply, mul_one, mul_neg,
      Finset.sum_neg_distrib]
    ring
  have hsym : ∀ j : Fin n, G (Fin.last n) j.castSucc = G j.castSucc (Fin.last n) :=
    fun j => (hG.apply (Fin.last n) j.castSucc).symm
  have hSb : (∑ j : Fin n, G (Fin.last n) j.castSucc * (A⁻¹ *ᵥ b) j)
      = ∑ k : Fin n, (A⁻¹ *ᵥ b) k * G k.castSucc (Fin.last n) :=
    Finset.sum_congr rfl (fun j _ => by rw [hsym j]; ring)
  have htransform : (∑ x : Fin n, -((A⁻¹ *ᵥ b) x) *
        (G x.castSucc (Fin.last n) - ∑ j : Fin n, G x.castSucc j.castSucc * (A⁻¹ *ᵥ b) j))
      = (∑ x : Fin n, (A⁻¹ *ᵥ b) x * ∑ j : Fin n, G x.castSucc j.castSucc * (A⁻¹ *ᵥ b) j)
        - ∑ x : Fin n, (A⁻¹ *ᵥ b) x * G x.castSucc (Fin.last n) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _; ring
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp only [key]
  simp only [schurVector, Fin.snoc_castSucc, Fin.snoc_last, Pi.neg_apply, one_mul]
  rw [htransform, hSb]
  ring

/-- **Block Schur relation (self-contained).**  For a matrix `G` with the bordered-prefix
block structure (prefix `A`, last column/row prefix `b`, corner `c`) and an invertible
prefix, the Schur vector `Fin.snoc (-u) 1` with `u = A⁻¹ b` satisfies
`G *ᵥ (Fin.snoc (-u) 1) = Fin.snoc 0 (c - b ⬝ᵥ u)`.  Native, positivity-free analogue of
`criticalVector_mulVec`. -/
theorem schurRelation {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ)
    (u : Fin n → ℝ) (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hGA : ∀ i j, G i.castSucc j.castSucc = A i j)
    (hGb : ∀ i, G i.castSucc (Fin.last n) = b i)
    (hGbt : ∀ j, G (Fin.last n) j.castSucc = b j)
    (hGc : G (Fin.last n) (Fin.last n) = c)
    (hAu : A *ᵥ u = b) :
    G *ᵥ Fin.snoc (-u) (1 : ℝ) = Fin.snoc 0 (c - b ⬝ᵥ u) := by
  have hrow : ∀ i : Fin n, (∑ j, A i j * u j) = b i := fun i => by
    have h := congrFun hAu i
    simpa [Matrix.mulVec, dotProduct] using h
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, Pi.neg_apply, mul_one, mul_neg, hGbt, hGc, Finset.sum_neg_distrib]
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, Pi.neg_apply, Pi.zero_apply, mul_one, mul_neg, hGA, hGb,
      Finset.sum_neg_distrib]
    rw [hrow i]
    ring

/-- **The Schur relation for `schurVector`, discharged.**  With an invertible prefix `A`,
`G *ᵥ schurVector A b = Fin.snoc 0 (c - b ⬝ᵥ (A⁻¹ *ᵥ b))`: the pivot in the last slot, no
hypotheses left for `schurVector_pivot`. -/
theorem schurVector_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ)
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hGA : ∀ i j, G i.castSucc j.castSucc = A i j)
    (hGb : ∀ i, G i.castSucc (Fin.last n) = b i)
    (hGbt : ∀ j, G (Fin.last n) j.castSucc = b j)
    (hGc : G (Fin.last n) (Fin.last n) = c)
    (hA : IsUnit A) :
    G *ᵥ schurVector A b = Fin.snoc 0 (c - b ⬝ᵥ (A⁻¹ *ᵥ b)) := by
  have hAu : A *ᵥ (A⁻¹ *ᵥ b) = b := by
    have hdet : IsUnit A.det := by rw [← Matrix.isUnit_iff_isUnit_det]; exact hA
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  simpa only [schurVector] using schurRelation A b c (A⁻¹ *ᵥ b) G hGA hGb hGbt hGc hAu

/-- **Pivot as a sandwich, fully discharged.**  Combining the native block Schur relation
with `schurVector_pivot`: for the bordered-prefix `G` with invertible prefix `A`,
`schurVector A b ⬝ᵥ (G *ᵥ schurVector A b) = c - b ⬝ᵥ (A⁻¹ *ᵥ b)` — the Schur pivot — with
no hypotheses beyond the block structure and invertibility.  Positivity-free. -/
theorem schurVector_pivot_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ)
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hGA : ∀ i j, G i.castSucc j.castSucc = A i j)
    (hGb : ∀ i, G i.castSucc (Fin.last n) = b i)
    (hGbt : ∀ j, G (Fin.last n) j.castSucc = b j)
    (hGc : G (Fin.last n) (Fin.last n) = c)
    (hA : IsUnit A) :
    schurVector A b ⬝ᵥ (G *ᵥ schurVector A b) = c - b ⬝ᵥ (A⁻¹ *ᵥ b) :=
  schurVector_pivot A b _ G (schurVector_mulVec A b c G hGA hGb hGbt hGc hA)

/-- **`hnorm` discharged.**  The Euclidean inner product of `e_last = toLp (single last 1)`
with the lifted Schur vector is `1` (its last coordinate). -/
theorem inner_eLast_schurVector (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (⟪(WithLp.toLp 2 (Pi.single (Fin.last n) (1 : ℝ)) : EuclideanSpace ℝ (Fin (n + 1))),
      WithLp.toLp 2 (schurVector A b)⟫ : ℝ) = 1 := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, schurVector, Fin.snoc_last, Pi.single_apply, Pi.star_apply, star_trivial]

/-- **`hrel` discharged (lifted).**  Through `toEuclideanCLM` and `toLp`, the block Schur
relation becomes `toEuclideanCLM G (toLp sv) = p • toLp (single last 1)`, i.e. the operator
sends the lifted Schur vector to the pivot times `e_last`.  Positivity-free. -/
theorem toEuclideanCLM_schurVector (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ)
    (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hGA : ∀ i j, G i.castSucc j.castSucc = A i j)
    (hGb : ∀ i, G i.castSucc (Fin.last n) = b i)
    (hGbt : ∀ j, G (Fin.last n) j.castSucc = b j)
    (hGc : G (Fin.last n) (Fin.last n) = c)
    (hA : IsUnit A) :
    toEuclideanCLM (𝕜 := ℝ) G (WithLp.toLp 2 (schurVector A b))
      = (c - b ⬝ᵥ (A⁻¹ *ᵥ b)) •
          (WithLp.toLp 2 (Pi.single (Fin.last n) 1) : EuclideanSpace ℝ (Fin (n + 1))) := by
  have hsnoc : (Fin.snoc 0 (c - b ⬝ᵥ (A⁻¹ *ᵥ b)) : Fin (n + 1) → ℝ)
      = (c - b ⬝ᵥ (A⁻¹ *ᵥ b)) • Pi.single (Fin.last n) 1 := by
    funext i
    refine Fin.lastCases ?_ ?_ i <;>
      simp [Fin.snoc_last, Fin.snoc_castSucc]
  rw [toEuclideanCLM_toLp, schurVector_mulVec A b c G hGA hGb hGbt hGc hA, hsnoc]
  rfl
