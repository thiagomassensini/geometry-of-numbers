import GeometryOfNumbers.Analysis.LogarithmicMomentHankel
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# All-order positivity from one Gram realization

The finite Hankel matrices are positive because they are Gram sections of one
feature family.  This file isolates the exact analytic input required from the
completed Green/gamma identity: a single feature map whose pairings reproduce
all unshifted moments, and a second feature map for all shifted moments.

No finite order is privileged.  Once either representation is supplied, the
corresponding positivity theorem holds simultaneously at every order.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

/-- A single Hilbert-space feature family realizes the full Hankel moment
kernel.  This is the precise output expected from the completed even Green
channel. -/
def IsMomentGramRepresentation
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (moments : ℕ → ℝ) (feature : ℕ → E) : Prop :=
  ∀ i j : ℕ, moments (i + j) = Matrix.gram ℝ feature i j

/-- A feature family realizes the shifted moment kernel.  Analytically this is
the positivity channel with one extra spectral coordinate. -/
def IsShiftedMomentGramRepresentation
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (moments : ℕ → ℝ) (feature : ℕ → E) : Prop :=
  ∀ i j : ℕ, moments (i + j + 1) = Matrix.gram ℝ feature i j

/-- One full Gram representation makes every finite Hankel section positive
semidefinite. -/
theorem hankelGram_posSemidef_of_gramRepresentation
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsMomentGramRepresentation moments feature)
    (N : ℕ) :
    (hankelGram moments N).PosSemidef := by
  have hmatrix :
      hankelGram moments N =
        Matrix.gram ℝ (fun i : Fin N ↦ feature (i : ℕ)) := by
    ext i j
    exact hrep (i : ℕ) (j : ℕ)
  rw [hmatrix]
  exact Matrix.posSemidef_gram ℝ _

/-- Linear independence of each finite feature prefix upgrades the Hankel
section from semidefinite to definite, which is the exact hypothesis needed
for an invertible Cholesky factor. -/
theorem hankelGram_posDef_of_gramRepresentation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsMomentGramRepresentation moments feature)
    (N : ℕ)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (hankelGram moments N).PosDef := by
  have hmatrix :
      hankelGram moments N =
        Matrix.gram ℝ (fun i : Fin N ↦ feature (i : ℕ)) := by
    ext i j
    exact hrep (i : ℕ) (j : ℕ)
  rw [hmatrix]
  exact Matrix.posDef_gram_of_linearIndependent hli

/-- One shifted Gram representation makes every shifted Hankel section
positive semidefinite. -/
theorem shiftedHankel_posSemidef_of_gramRepresentation
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) :
    (shiftedHankel moments N).PosSemidef := by
  have hmatrix :
      shiftedHankel moments N =
        Matrix.gram ℝ (fun i : Fin N ↦ feature (i : ℕ)) := by
    ext i j
    exact hrep (i : ℕ) (j : ℕ)
  rw [hmatrix]
  exact Matrix.posSemidef_gram ℝ _

/-- Linear independence of the shifted feature prefix gives strict shifted
positivity at the selected order. -/
theorem shiftedHankel_posDef_of_gramRepresentation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (shiftedHankel moments N).PosDef := by
  have hmatrix :
      shiftedHankel moments N =
        Matrix.gram ℝ (fun i : Fin N ↦ feature (i : ℕ)) := by
    ext i j
    exact hrep (i : ℕ) (j : ℕ)
  rw [hmatrix]
  exact Matrix.posDef_gram_of_linearIndependent hli

end

end GeometryOfNumbers.Analysis
