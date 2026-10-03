import GeometryOfNumbers.Analysis.FiniteJacobiTransport
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Tactic

/-!
# Canonical exact whitening from the LDL decomposition

For a positive definite Hankel Gram matrix, Mathlib's LDL construction gives
a canonical lower-triangular inverse factor `H` with

`H G Hᵀ = D`.

Rescaling each row by the inverse square root of the corresponding positive
diagonal entry produces `B G Bᵀ = I`.  This is the exact normalized
Gram--Schmidt/Cholesky whitening used by the Jacobi construction; no fitted
matrix or spectral-height data enters the definition.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

/-- Every diagonal entry in the LDL decomposition of a real positive
definite matrix is strictly positive. -/
theorem LDL_diagEntries_pos
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) (i : Fin N) :
    0 < LDL.diagEntries hgram i := by
  have hdiag : (LDL.diag hgram).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj hgram]
    exact hgram.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_invertible
        (LDL.lowerInv hgram))
  simpa [LDL.diag] using hdiag.diag_pos (i := i)

/-- Positive diagonal rescaling which normalizes the LDL diagonal. -/
def canonicalLDLScale
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) (i : Fin N) : ℝ :=
  (Real.sqrt (LDL.diagEntries hgram i))⁻¹

theorem canonicalLDLScale_pos
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) (i : Fin N) :
    0 < canonicalLDLScale hgram i := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (LDL_diagEntries_pos hgram i))

/-- Canonical normalized inverse factor: diagonal normalization followed by
the lower inverse factor from LDL/Gram--Schmidt. -/
def canonicalLDLInverseFactor
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (canonicalLDLScale hgram) *
    LDL.lowerInv hgram

/-- The canonical inverse factor remains lower triangular. -/
theorem canonicalLDLInverseFactor_triangular
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) {i j : Fin N} (hij : i < j) :
    canonicalLDLInverseFactor hgram i j = 0 := by
  simp [canonicalLDLInverseFactor,
    LDL.lowerInv_triangular hgram hij]

/-- The positive LDL diagonal is normalized exactly to the identity. -/
theorem canonicalLDL_diagonal_normalization
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) :
    Matrix.diagonal (canonicalLDLScale hgram) *
        LDL.diag hgram *
        Matrix.diagonal (canonicalLDLScale hgram) = 1 := by
  rw [LDL.diag]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply, if_pos]
    have hd := LDL_diagEntries_pos hgram i
    have hsqrt : Real.sqrt (LDL.diagEntries hgram i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hd)
    rw [canonicalLDLScale]
    calc
      (Real.sqrt (LDL.diagEntries hgram i))⁻¹ *
            LDL.diagEntries hgram i *
            (Real.sqrt (LDL.diagEntries hgram i))⁻¹ =
          (Real.sqrt (LDL.diagEntries hgram i))⁻¹ *
            (Real.sqrt (LDL.diagEntries hgram i)) ^ 2 *
            (Real.sqrt (LDL.diagEntries hgram i))⁻¹ := by
              rw [Real.sq_sqrt hd.le]
      _ = 1 := by field_simp [hsqrt]
  · simp [hij]

/-- The canonical LDL factor whitens the positive definite matrix exactly. -/
theorem canonicalLDLInverseFactor_whitens
    {N : ℕ} {gram : Matrix (Fin N) (Fin N) ℝ}
    (hgram : gram.PosDef) :
    finiteJacobiTransport (canonicalLDLInverseFactor hgram) gram = 1 := by
  have hldl :
      LDL.diag hgram =
        LDL.lowerInv hgram * gram *
          (LDL.lowerInv hgram).transpose := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      LDL.diag_eq_lowerInv_conj hgram
  calc
    finiteJacobiTransport (canonicalLDLInverseFactor hgram) gram =
        Matrix.diagonal (canonicalLDLScale hgram) *
          (LDL.lowerInv hgram * gram *
            (LDL.lowerInv hgram).transpose) *
          Matrix.diagonal (canonicalLDLScale hgram) := by
      simp [finiteJacobiTransport, canonicalLDLInverseFactor,
        Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Matrix.diagonal (canonicalLDLScale hgram) *
          LDL.diag hgram *
          Matrix.diagonal (canonicalLDLScale hgram) := by
      rw [hldl]
    _ = 1 := canonicalLDL_diagonal_normalization hgram

/-- Canonical finite whitening for every positive definite Hankel section. -/
def canonicalHankelWhitening
    (moments : ℕ → ℝ) (N : ℕ)
    (hgram : (hankelGram moments N).PosDef) :
    FiniteGramWhitening moments N :=
  FiniteGramWhitening.ofIdentity moments N
    (canonicalLDLInverseFactor hgram)
    (canonicalLDLInverseFactor_whitens hgram)

end

end GeometryOfNumbers.Analysis
