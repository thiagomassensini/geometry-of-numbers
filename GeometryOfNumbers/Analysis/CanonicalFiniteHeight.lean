import GeometryOfNumbers.Analysis.CanonicalLDLWhitening
import GeometryOfNumbers.Analysis.FiniteHeightOperator

open scoped BigOperators

/-!
# Canonical finite Jacobi and height operators

This file removes the last freely supplied matrix from the finite native
construction. Once the Hankel section `G_N` is positive definite, its
normalized LDL decomposition determines the whitening factor canonically.
The shifted section `K_N` is then transported by that factor, and the finite
height operator is obtained by the exact functional calculus `J_N^(-1/2)`.

Neither definition accepts a list of zeta-zero heights or a fitted matrix.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

/-- The canonical finite Jacobi section determined by the moment sequence. -/
def canonicalFiniteJacobiSection
    (moments : ℕ → ℝ) (N : ℕ)
    (hgram : (hankelGram moments N).PosDef) :
    Matrix (Fin N) (Fin N) ℝ :=
  finiteJacobiSection moments N
    (canonicalHankelWhitening moments N hgram)

/-- A shifted Gram realization with independent finite prefix makes the
canonical Jacobi section strictly positive. -/
theorem canonicalFiniteJacobiSection_posDef_of_shiftedGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (canonicalFiniteJacobiSection moments N hgram).PosDef := by
  exact finiteJacobiSection_posDef_of_shiftedGram hrep N
    (canonicalHankelWhitening moments N hgram) hli

/-- The canonical finite height operator generated solely from the moment
Hankel pair and its positivity certificates. -/
def canonicalFiniteHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    Matrix (Fin N) (Fin N) ℝ :=
  finiteHeightOperator
    (canonicalFiniteJacobiSection_posDef_of_shiftedGram
      hrep N hgram hli)

/-- The canonical finite native operator is self-adjoint without the
post-processing symmetrization used by floating-point implementations. -/
theorem canonicalFiniteHeightOperator_isSymm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (canonicalFiniteHeightOperator hrep N hgram hli).IsSymm := by
  exact finiteHeightOperator_isSymm
    (canonicalFiniteJacobiSection_posDef_of_shiftedGram
      hrep N hgram hli)

/-- Exact spectral readout for the canonical finite height operator. -/
theorem canonicalFiniteHeightOperator_charpoly
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (hgram : (hankelGram moments N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (canonicalFiniteHeightOperator hrep N hgram hli).charpoly =
      ∏ i : Fin N,
        (Polynomial.X - Polynomial.C
          (finiteHeightEigenvalue
            (canonicalFiniteJacobiSection_posDef_of_shiftedGram
              hrep N hgram hli) i)) := by
  exact finiteHeightOperator_charpoly
    (canonicalFiniteJacobiSection_posDef_of_shiftedGram
      hrep N hgram hli)

end

end GeometryOfNumbers.Analysis
