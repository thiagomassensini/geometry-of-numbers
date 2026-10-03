import GeometryOfNumbers.Analysis.FiniteJacobiTransport
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite height operator

For a positive definite Jacobi section `J_N`, the height operator is defined
by the Hermitian functional calculus with the scalar function

`y ↦ 1 / sqrt(y)`.

The characteristic-polynomial theorem below proves that its eigenvalues are
exactly the transformed Jacobi eigenvalues.  No table of target heights is an
input to this definition.
-/

open scoped BigOperators

namespace GeometryOfNumbers.Analysis

noncomputable section

/-- The positive height attached to one positive Jacobi eigenvalue. -/
def finiteHeightEigenvalue
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) (i : Fin N) : ℝ :=
  (Real.sqrt (hjacobi.isHermitian.eigenvalues i))⁻¹

/-- Every finite height eigenvalue is strictly positive. -/
theorem finiteHeightEigenvalue_pos
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) (i : Fin N) :
    0 < finiteHeightEigenvalue hjacobi i := by
  apply inv_pos.mpr
  exact Real.sqrt_pos.2 (hjacobi.eigenvalues_pos i)

/-- Exact finite operator `T_N = J_N^(-1/2)` obtained from the Hermitian
functional calculus. -/
def finiteHeightOperator
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) : Matrix (Fin N) (Fin N) ℝ :=
  hjacobi.isHermitian.cfc (fun y : ℝ ↦ (Real.sqrt y)⁻¹)

/-- The finite height operator is exactly symmetric, hence self-adjoint in
finite dimension. No numerical symmetrization step is required. -/
theorem finiteHeightOperator_isSymm
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) :
    (finiteHeightOperator hjacobi).IsSymm := by
  rw [finiteHeightOperator,
    ← Matrix.IsHermitian.cfc_eq hjacobi.isHermitian]
  exact Matrix.isHermitian_iff_isSymm.mp
    (cfc_predicate (fun y : ℝ ↦ (Real.sqrt y)⁻¹) jacobi)

/-- The spectrum is transformed exactly: the characteristic polynomial of
`T_N` has roots `1 / sqrt(lambda_i(J_N))`. -/
theorem finiteHeightOperator_charpoly
    {N : ℕ} {jacobi : Matrix (Fin N) (Fin N) ℝ}
    (hjacobi : jacobi.PosDef) :
    (finiteHeightOperator hjacobi).charpoly =
      ∏ i : Fin N,
        (Polynomial.X - Polynomial.C (finiteHeightEigenvalue hjacobi i)) := by
  rw [finiteHeightOperator,
    ← Matrix.IsHermitian.cfc_eq hjacobi.isHermitian]
  simpa [finiteHeightEigenvalue] using
    (Matrix.IsHermitian.charpoly_cfc_eq hjacobi.isHermitian
      (fun y : ℝ ↦ (Real.sqrt y)⁻¹))

/-- The native finite height operator obtained from shifted Gram data and an
exact Gram whitening. -/
def nativeFiniteHeightOperator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (whitening : FiniteGramWhitening moments N)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    Matrix (Fin N) (Fin N) ℝ :=
  finiteHeightOperator
    (finiteJacobiSection_posDef_of_shiftedGram hrep N whitening hli)

/-- The characteristic polynomial of the native finite height operator is
the product over the inverse-square-root Jacobi eigenvalues generated from
the moments. -/
theorem nativeFiniteHeightOperator_charpoly
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (whitening : FiniteGramWhitening moments N)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (nativeFiniteHeightOperator hrep N whitening hli).charpoly =
      ∏ i : Fin N,
        (Polynomial.X - Polynomial.C
          (finiteHeightEigenvalue
            (finiteJacobiSection_posDef_of_shiftedGram hrep N whitening hli)
            i)) := by
  exact finiteHeightOperator_charpoly
    (finiteJacobiSection_posDef_of_shiftedGram hrep N whitening hli)

end

end GeometryOfNumbers.Analysis
