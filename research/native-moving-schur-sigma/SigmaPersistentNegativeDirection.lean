import SigmaCertifiedNegativeDirection
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Persistence of negative directions in larger Hankel sections

The `sigmaMatrix` sections are nested principal blocks: increasing the section
size does not change any entry in the old leading block. Positive
semidefiniteness passes to every principal submatrix, so a negative direction
in one section rules out positive semidefiniteness in every larger section.
-/

namespace CarrySigmaObstruction

open CarryMovingSigma Matrix
open scoped BigOperators Matrix

noncomputable section
set_option autoImplicit false

/-- The smaller sigma matrix is the leading principal submatrix of every
larger section. -/
theorem sigmaMatrix_prefix_submatrix (d : ℝ) (s N M : ℕ) (hNM : N ≤ M) :
    (sigmaMatrix d s M).submatrix (Fin.castLE hNM) (Fin.castLE hNM) =
      sigmaMatrix d s N := by
  ext i j
  rfl

/-- A negative quadratic form on a leading principal block contradicts
positive semidefiniteness of the full section. -/
theorem sigmaMatrix_not_posSemidef_of_negative_direction
    (d : ℝ) (s N : ℕ) (v : Fin N → ℝ)
    (hneg : v ⬝ᵥ (sigmaMatrix d s N *ᵥ v) < 0)
    (M : ℕ) (hNM : N ≤ M) :
    ¬ (sigmaMatrix d s M).PosSemidef := by
  intro hM
  have hprefix := hM.submatrix (Fin.castLE hNM)
  rw [sigmaMatrix_prefix_submatrix d s N M hNM] at hprefix
  have hnonneg := hprefix.dotProduct_mulVec_nonneg v
  have hnonneg' : 0 ≤ v ⬝ᵥ (sigmaMatrix d s N *ᵥ v) := by
    simpa [Pi.star_apply, star_trivial] using hnonneg
  linarith

/-- For every sufficiently large dimension, the original sigma matrix has a
strictly negative direction. The proof uses only its nested principal blocks. -/
theorem certified_sigma_negative_directions_persist
    (d : ℝ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ)) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      ∃ v : Fin M → ℝ, v ≠ 0 ∧
        v ⬝ᵥ (sigmaMatrix d 0 M *ᵥ v) < 0 := by
  obtain ⟨N, v, _, hneg⟩ :=
    certified_sigma_negative_direction_of_nonzero_small_shift d hd₀ hd₁
  refine ⟨N, fun M hNM => ?_⟩
  have hnot : ¬ (sigmaMatrix d 0 M).PosSemidef :=
    sigmaMatrix_not_posSemidef_of_negative_direction d 0 N v hneg M hNM
  let A := sigmaMatrix d 0 M
  have hsymm : A.IsSymm := by
    simpa [A] using CarryMovingSigma.sigma_matrix_symm d 0 M
  have hHerm : A.IsHermitian := by simpa using hsymm
  have hnotQuad : ¬ ∀ w : Fin M → ℝ, 0 ≤ star w ⬝ᵥ (A *ᵥ w) := by
    intro hquad
    apply hnot
    exact Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm, hquad⟩
  push Not at hnotQuad
  obtain ⟨w, hw⟩ := hnotQuad
  have hwneg : w ⬝ᵥ (A *ᵥ w) < 0 := by
    simpa [Pi.star_apply, star_trivial] using hw
  have hwne : w ≠ 0 := by
    intro hw0
    subst w
    simp at hwneg
  exact ⟨w, hwne, by simpa [A] using hwneg⟩

/-- In particular, every section at or beyond the first negative one fails
positive semidefiniteness. -/
theorem certified_sigma_not_posSemidef_persist
    (d : ℝ) (hd₀ : 0 < |d|) (hd₁ : |d| < (1 / 4 : ℝ)) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M → ¬ (sigmaMatrix d 0 M).PosSemidef := by
  obtain ⟨N, hN⟩ := certified_sigma_negative_directions_persist d hd₀ hd₁
  refine ⟨N, fun M hNM hM => ?_⟩
  obtain ⟨v, hv, hneg⟩ := hN M hNM
  have hnonneg := hM.dotProduct_mulVec_nonneg v
  have hnonneg' : 0 ≤ v ⬝ᵥ (sigmaMatrix d 0 M *ᵥ v) := by
    simpa [Pi.star_apply, star_trivial] using hnonneg
  linarith

end
end CarrySigmaObstruction

#print axioms CarrySigmaObstruction.sigmaMatrix_prefix_submatrix
#print axioms CarrySigmaObstruction.certified_sigma_negative_directions_persist
#print axioms CarrySigmaObstruction.certified_sigma_not_posSemidef_persist
