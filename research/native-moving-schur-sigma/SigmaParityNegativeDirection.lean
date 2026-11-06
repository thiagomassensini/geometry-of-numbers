import SigmaPadeEventualNegativity
import SigmaPersistentNegativeDirection
import Mathlib.Analysis.Matrix.PosDef

/-!
# Eventual negative directions in the even and odd sigma sectors

The negative Padé minors with indices `2 * i` and `2 * i + 1` are the determinants
of the corresponding two by two windows in `sigmaMatrix d 0` and `sigmaMatrix d 1`.
Each such window is a principal submatrix of every sufficiently large section, so
its negative direction extends to all larger dimensions.
-/

namespace CarrySigmaObstruction

open CarryMovingSigma Matrix
open CarrySigmaPade
open scoped BigOperators Matrix

noncomputable section
set_option autoImplicit false

/-- A negative original Padé minor gives a negative direction in its two by two
sigma window. -/
theorem sigmaMatrix_negative_direction_of_negative_pade_minor
    (d : ℝ) (p : ℕ) (hD : sigmaPadeD d p < 0) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧
      v ⬝ᵥ (sigmaMatrix d p 2 *ᵥ v) < 0 := by
  have hnot : ¬ (sigmaMatrix d p 2).PosSemidef := by
    intro hpsd
    have hdetD : 0 ≤ sigmaPadeD d p := by
      rw [← sigmaPencilGram_det d p]
      simpa [sigmaPencilGram] using hpsd.det_nonneg
    linarith
  let A : Matrix (Fin 2) (Fin 2) ℝ := sigmaMatrix d p 2
  have hsymm : A.IsSymm := by
    simpa [A] using CarryMovingSigma.sigma_matrix_symm d p 2
  have hHerm : A.IsHermitian := by simpa using hsymm
  have hnotQuad : ¬ ∀ w : Fin 2 → ℝ, 0 ≤ star w ⬝ᵥ (A *ᵥ w) := by
    intro hquad
    apply hnot
    exact Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hHerm, hquad⟩
  push Not at hnotQuad
  obtain ⟨v, hv⟩ := hnotQuad
  have hvneg : v ⬝ᵥ (A *ᵥ v) < 0 := by
    simpa [Pi.star_apply, star_trivial] using hv
  have hvne : v ≠ 0 := by
    intro hv0
    subst v
    simp at hvneg
  exact ⟨v, hvne, by simpa [A] using hvneg⟩

/-- Embed the two consecutive indices beginning at `i` into a larger sigma
section. -/
def sigmaParityWindowEmbedding (i M : ℕ) (hIM : i + 2 ≤ M) : Fin 2 → Fin M :=
  fun j => ⟨i + j.val, by omega⟩

/-- The window beginning at index `i` is exactly the shifted two by two sigma
matrix, with shift increased by `2 * i`. -/
theorem sigmaMatrix_window_submatrix (d : ℝ) (s M i : ℕ)
    (hIM : i + 2 ≤ M) :
    (sigmaMatrix d s M).submatrix
        (sigmaParityWindowEmbedding i M hIM)
        (sigmaParityWindowEmbedding i M hIM) =
      sigmaMatrix d (s + 2 * i) 2 := by
  ext j k
  change CarrySigmaSource.completedSigmaLogJet d
      ((i + j.val) + (i + k.val) + s) =
    CarrySigmaSource.completedSigmaLogJet d (j.val + k.val + (s + 2 * i))
  congr 1
  ring

/-- A negative shifted window makes the section ending at that window fail
positive semidefiniteness. -/
theorem sigmaMatrix_not_posSemidef_of_shifted_window
    (d : ℝ) (s i : ℕ) (v : Fin 2 → ℝ)
    (hneg : v ⬝ᵥ (sigmaMatrix d (s + 2 * i) 2 *ᵥ v) < 0) :
    ¬ (sigmaMatrix d s (i + 2)).PosSemidef := by
  intro hM
  have hsub := hM.submatrix (sigmaParityWindowEmbedding i (i + 2) (by omega))
  rw [sigmaMatrix_window_submatrix d s (i + 2) i (by omega)] at hsub
  have hnonneg := hsub.dotProduct_mulVec_nonneg v
  have hnonneg' : 0 ≤ v ⬝ᵥ (sigmaMatrix d (s + 2 * i) 2 *ᵥ v) := by
    simpa [Pi.star_apply, star_trivial] using hnonneg
  linarith

/-- Symmetry turns failure of positive semidefiniteness into an explicit
negative real direction. -/
theorem sigmaMatrix_negative_direction_of_not_posSemidef
    (d : ℝ) (s N : ℕ) (hnot : ¬ (sigmaMatrix d s N).PosSemidef) :
    ∃ w : Fin N → ℝ, w ≠ 0 ∧
      w ⬝ᵥ (sigmaMatrix d s N *ᵥ w) < 0 := by
  let A : Matrix (Fin N) (Fin N) ℝ := sigmaMatrix d s N
  have hsymm : A.IsSymm := by
    simpa [A] using CarryMovingSigma.sigma_matrix_symm d s N
  have hHerm : A.IsHermitian := by simpa using hsymm
  have hnotQuad : ¬ ∀ z : Fin N → ℝ, 0 ≤ star z ⬝ᵥ (A *ᵥ z) := by
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

/-- A negative shifted window gives a negative direction in its complete
prefix section. -/
theorem sigmaMatrix_negative_direction_of_shifted_window
    (d : ℝ) (s i : ℕ) (v : Fin 2 → ℝ)
    (hneg : v ⬝ᵥ (sigmaMatrix d (s + 2 * i) 2 *ᵥ v) < 0) :
    ∃ w : Fin (i + 2) → ℝ, w ≠ 0 ∧
      w ⬝ᵥ (sigmaMatrix d s (i + 2) *ᵥ w) < 0 := by
  exact sigmaMatrix_negative_direction_of_not_posSemidef d s (i + 2)
    (sigmaMatrix_not_posSemidef_of_shifted_window d s i v hneg)

/-- C1B transports the negative direction in the complete prefix section to
every larger dimension in the same parity sector. -/
theorem sigmaMatrix_negative_directions_of_window
    (d : ℝ) (s M i : ℕ) (hIM : i + 2 ≤ M)
    (v : Fin 2 → ℝ)
    (hneg : v ⬝ᵥ (sigmaMatrix d (s + 2 * i) 2 *ᵥ v) < 0) :
    ∃ w : Fin M → ℝ, w ≠ 0 ∧
      w ⬝ᵥ (sigmaMatrix d s M *ᵥ w) < 0 := by
  obtain ⟨u, hu, huneg⟩ := sigmaMatrix_negative_direction_of_shifted_window d s i v hneg
  have hnot : ¬ (sigmaMatrix d s M).PosSemidef :=
    sigmaMatrix_not_posSemidef_of_negative_direction d s (i + 2) u huneg M hIM
  exact sigmaMatrix_negative_direction_of_not_posSemidef d s M hnot

/-- The even Padé windows `p = 2 * i` yield negative directions in every
sufficiently large section of the even sector `sigmaMatrix (1/5) 0`. -/
theorem exists_even_sigma_negative_directions_from_pade :
    ∃ i₀ : ℕ, ∀ M : ℕ, i₀ + 2 ≤ M →
      ∃ v : Fin M → ℝ, v ≠ 0 ∧
        v ⬝ᵥ (sigmaMatrix (1 / 5) 0 M *ᵥ v) < 0 := by
  obtain ⟨P, hP⟩ := exists_eventually_negative_sigmaPadeD_from_height50_certificate
  have hminor : sigmaPadeD (1 / 5) (2 * P) < 0 := by
    apply hP
    omega
  obtain ⟨v, _, hneg⟩ :=
    sigmaMatrix_negative_direction_of_negative_pade_minor (1 / 5) (2 * P) hminor
  refine ⟨P, fun M hPM => ?_⟩
  have hneg' : v ⬝ᵥ (sigmaMatrix (1 / 5) (0 + 2 * P) 2 *ᵥ v) < 0 := by
    simpa using hneg
  exact sigmaMatrix_negative_directions_of_window
    (1 / 5) 0 M P hPM v hneg'

/-- The odd Padé windows `p = 2 * i + 1` yield negative directions in every
sufficiently large section of the odd sector `sigmaMatrix (1/5) 1`. -/
theorem exists_odd_sigma_negative_directions_from_pade :
    ∃ i₀ : ℕ, ∀ M : ℕ, i₀ + 2 ≤ M →
      ∃ v : Fin M → ℝ, v ≠ 0 ∧
        v ⬝ᵥ (sigmaMatrix (1 / 5) 1 M *ᵥ v) < 0 := by
  obtain ⟨P, hP⟩ := exists_eventually_negative_sigmaPadeD_from_height50_certificate
  have hminor : sigmaPadeD (1 / 5) (2 * P + 1) < 0 := by
    apply hP
    omega
  obtain ⟨v, _, hneg⟩ :=
    sigmaMatrix_negative_direction_of_negative_pade_minor (1 / 5) (2 * P + 1) hminor
  refine ⟨P, fun M hPM => ?_⟩
  have hneg' : v ⬝ᵥ (sigmaMatrix (1 / 5) (1 + 2 * P) 2 *ᵥ v) < 0 := by
    have hindex : 1 + 2 * P = 2 * P + 1 := by omega
    rw [hindex]
    exact hneg
  exact sigmaMatrix_negative_directions_of_window
    (1 / 5) 1 M P hPM v hneg'

end
end CarrySigmaObstruction

#print axioms CarrySigmaObstruction.sigmaMatrix_negative_direction_of_negative_pade_minor
#print axioms CarrySigmaObstruction.sigmaMatrix_negative_directions_of_window
#print axioms CarrySigmaObstruction.exists_even_sigma_negative_directions_from_pade
#print axioms CarrySigmaObstruction.exists_odd_sigma_negative_directions_from_pade
