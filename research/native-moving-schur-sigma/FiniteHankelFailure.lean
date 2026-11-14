import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Nat.Find
import MomentLogConvexity

/-!
# Finite first-failure and generalized Schur classification

The block-form result is independent of the moment source. It separates a negative
extension of a positive semidefinite prefix into a kernel-crossing case and a
generalized Schur-residual case. The latter permits a singular leading block.
-/

open scoped InnerProductSpace Matrix
open CarryMomentLogConvex

noncomputable section

namespace FiniteHankelFailure


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The quadratic form of a symmetric block extension with leading operator `A`,
cross term `b`, and final diagonal entry `c`. -/
def blockQuadratic (A : E →ₗ[ℝ] E) (b : E) (c : ℝ) (x : E) (t : ℝ) : ℝ :=
  ⟪x, A x⟫_ℝ + 2 * t * ⟪b, x⟫_ℝ + c * t ^ 2

omit [FiniteDimensional ℝ E] in
/-- A nonzero coupling to a null direction forces the block extension to have
negative quadratic energy. The witness is the null direction scaled against the
new coordinate. -/
theorem kernel_crossing_negative
    (A : E →ₗ[ℝ] E) (b : E) (c : ℝ)
    (hcross : ∃ w, A w = 0 ∧ ⟪b, w⟫_ℝ ≠ 0) :
    ∃ x t, blockQuadratic A b c x t < 0 := by
  obtain ⟨w, hw, hβ⟩ := hcross
  let β := ⟪b, w⟫_ℝ
  let scale := -(c + 1) / (2 * β)
  refine ⟨scale • w, 1, ?_⟩
  have hq : blockQuadratic A b c (scale • w) 1 = -1 := by
    simp only [blockQuadratic, map_smul, hw, smul_zero, inner_zero_right,
      inner_smul_right, one_pow, mul_one]
    dsimp [scale, β]
    field_simp [hβ]
    ring
  rw [hq]
  norm_num

#print axioms kernel_crossing_negative

/-- Classification of a failed positive semidefinite block extension. If the old
block is positive semidefinite, then either the new column sees its kernel, or it
lies in the range and has a strictly negative generalized Schur residual. -/
theorem block_failure_classification
    (A : E →ₗ[ℝ] E) (b : E) (c : ℝ)
    (hA_symm : A.IsSymmetric)
    (hA_nonneg : ∀ x, 0 ≤ ⟪x, A x⟫_ℝ)
    (hblock_bad : ¬ ∀ x t, 0 ≤ blockQuadratic A b c x t) :
    (∃ w, A w = 0 ∧ ⟪b, w⟫_ℝ ≠ 0) ∨
      ∃ y, A y = b ∧ c - ⟪y, A y⟫_ℝ < 0 := by
  classical
  by_cases hcross : ∃ w, A w = 0 ∧ ⟪b, w⟫_ℝ ≠ 0
  · exact Or.inl hcross
  · right
    have hborth : b ∈ A.kerᗮ := by
      rw [Submodule.mem_orthogonal]
      intro w hw
      have hzero : ⟪b, w⟫_ℝ = 0 := by
        by_contra hne
        exact hcross ⟨w, hw, hne⟩
      simpa [real_inner_comm] using hzero
    have hbrange : b ∈ A.range := by
      rw [LinearMap.orthogonal_ker, hA_symm.adjoint_eq] at hborth
      exact hborth
    obtain ⟨y, hy⟩ := hbrange
    have hyA : A y = b := hy
    have hbad_exists : ∃ x t, blockQuadratic A b c x t < 0 := by
      by_contra h
      apply hblock_bad
      intro x t
      have hnonneg : ¬ blockQuadratic A b c x t < 0 := by
        intro hn
        exact h ⟨x, t, hn⟩
      exact le_of_not_gt hnonneg
    obtain ⟨x, t, hxt⟩ := hbad_exists
    have hquad_id : blockQuadratic A b c x t =
        ⟪x + t • y, A (x + t • y)⟫_ℝ + t ^ 2 * (c - ⟪y, A y⟫_ℝ) := by
      simp only [blockQuadratic, map_add, map_smul, inner_add_right, inner_add_left,
        inner_smul_right, inner_smul_left]
      rw [← hyA]
      have hsymm_inner : ⟪x, A y⟫_ℝ = ⟪y, A x⟫_ℝ := by
        rw [real_inner_comm, hA_symm]
      rw [← real_inner_comm (A y) x, hsymm_inner]
      simp only [starRingEnd_apply, star_trivial]
      ring
    have htne : t ≠ 0 := by
      intro ht
      subst t
      have : 0 ≤ blockQuadratic A b c x 0 := by
        simp [blockQuadratic, hA_nonneg]
      linarith
    have hresidual : c - ⟪y, A y⟫_ℝ < 0 := by
      by_contra hnot
      have hres_nonneg : 0 ≤ c - ⟪y, A y⟫_ℝ := le_of_not_gt hnot
      have hsq_nonneg : 0 ≤ ⟪x + t • y, A (x + t • y)⟫_ℝ := hA_nonneg _
      have hfactor_nonneg : 0 ≤ t ^ 2 * (c - ⟪y, A y⟫_ℝ) :=
        mul_nonneg (sq_nonneg t) hres_nonneg
      rw [hquad_id] at hxt
      linarith
    exact ⟨y, hyA, hresidual⟩

#print axioms block_failure_classification

omit [FiniteDimensional ℝ E] in
/-- Any two solutions of `A y = b` give the same generalized Schur residual.
This does not require `A` to be invertible. -/
lemma generalized_residual_independent
    (A : E →ₗ[ℝ] E) (b : E) (c : ℝ)
    (hA_symm : A.IsSymmetric) {y₁ y₂ : E}
    (hy₁ : A y₁ = b) (hy₂ : A y₂ = b) :
    c - ⟪y₁, A y₁⟫_ℝ = c - ⟪y₂, A y₂⟫_ℝ := by
  have hkernel : A (y₁ - y₂) = 0 := by rw [map_sub, hy₁, hy₂, sub_self]
  have hinner : ⟪y₁, b⟫_ℝ = ⟪y₂, b⟫_ℝ := by
    have hzero : ⟪y₁ - y₂, b⟫_ℝ = 0 := by
      rw [← hy₁, ← hA_symm (y₁ - y₂) y₁, hkernel]
      simp
    rw [← sub_eq_zero]
    simpa [inner_sub_left] using hzero
  rw [hy₁, hy₂]
  exact congrArg (fun z : ℝ => c - z) hinner

#print axioms generalized_residual_independent

omit [FiniteDimensional ℝ E] in
/-- With a solution to `A y = b`, nonnegativity of the entire block quadratic
form is equivalent to nonnegativity of its generalized Schur residual. -/
lemma block_nonneg_iff_generalized_residual_nonneg
    (A : E →ₗ[ℝ] E) (b : E) (c : ℝ) (y : E)
    (hA_symm : A.IsSymmetric)
    (hA_nonneg : ∀ x, 0 ≤ ⟪x, A x⟫_ℝ)
    (hy : A y = b) :
    (∀ x t, 0 ≤ blockQuadratic A b c x t) ↔
      0 ≤ c - ⟪y, A y⟫_ℝ := by
  have hquad_id : ∀ x t,
      blockQuadratic A b c x t =
        ⟪x + t • y, A (x + t • y)⟫_ℝ + t ^ 2 * (c - ⟪y, A y⟫_ℝ) := by
    intro x t
    simp only [blockQuadratic, map_add, map_smul, inner_add_right, inner_add_left,
      inner_smul_right, inner_smul_left]
    rw [← hy]
    have hsymm_inner : ⟪x, A y⟫_ℝ = ⟪y, A x⟫_ℝ := by
      rw [real_inner_comm, hA_symm]
    rw [← real_inner_comm (A y) x, hsymm_inner]
    simp only [starRingEnd_apply, star_trivial]
    ring
  constructor
  · intro hnonneg
    have h := hnonneg (-y) 1
    rw [hquad_id] at h
    simpa using h
  · intro hres x t
    rw [hquad_id]
    exact add_nonneg (hA_nonneg _) (mul_nonneg (sq_nonneg t) hres)

#print axioms block_nonneg_iff_generalized_residual_nonneg

/-- If a sequence of finite matrices fails positive semidefiniteness at some size,
there is a least such size; every strictly smaller prefix is positive semidefinite. -/
theorem exists_least_bad_size (M : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℝ)
    (hbad : ∃ N, ¬ (M N).PosSemidef) :
    ∃ N, ¬ (M N).PosSemidef ∧ ∀ m < N, (M m).PosSemidef := by
  classical
  let P : ℕ → Prop := fun n => ¬ (M n).PosSemidef
  have hP : ∃ n, P n := hbad
  let N := Nat.find hP
  refine ⟨N, Nat.find_spec hP, ?_⟩
  intro m hm
  by_contra hnot
  exact (Nat.find_min hP hm) hnot

#print axioms exists_least_bad_size

/-- For a real Hankel tower, the least failing positive-semidefinite size is positive:
the empty prefix is always positive semidefinite. -/
theorem exists_first_hankel_failure (h : ℕ → ℝ)
    (hbad : ∃ N, ¬ (hankelMatrix h N).PosSemidef) :
    ∃ N, 0 < N ∧ ¬ (hankelMatrix h N).PosSemidef ∧
      ∀ m < N, (hankelMatrix h m).PosSemidef := by
  obtain ⟨N, hNbad, hNsmall⟩ :=
    exists_least_bad_size (hankelMatrix h) hbad
  have hzero : (hankelMatrix h 0).PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, ?_⟩
    · ext i j
      exact Fin.elim0 i
    intro v
    simp
  have hNpos : 0 < N := by
    by_contra hnot
    have hNzero : N = 0 := by omega
    subst N
    exact hNbad hzero
  exact ⟨N, hNpos, hNbad, hNsmall⟩

#print axioms exists_first_hankel_failure

end FiniteHankelFailure
