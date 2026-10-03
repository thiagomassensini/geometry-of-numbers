import GeometryOfNumbers.Analysis.MomentGramPositivity

/-!
# Finite Jacobi transport

This module formalizes the matrix step implemented by the native reference
script.  A whitening factor for the Hankel Gram matrix transports the shifted
Hankel matrix by congruence:

`J_N = B_N K_N B_Nᵀ`, where `B_N = L_N⁻¹` in the Cholesky realization.

The construction is not a fitted matrix: both `G_N` and `K_N` come from the
same moment sequence, and the only additional datum is a factor that whitens
`G_N`.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

/-- Congruence transport on an arbitrary finite coordinate type.  This is the
coordinate-free finite algebra behind every native Jacobi section. -/
def jacobiCongruence {ι : Type*} [Fintype ι]
    (inverseGramFactor shifted : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  inverseGramFactor * shifted * inverseGramFactor.transpose

/-- Congruence transport used by the finite Jacobi construction. -/
def finiteJacobiTransport {N : ℕ}
    (inverseGramFactor shifted : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  inverseGramFactor * shifted * inverseGramFactor.transpose

@[simp] theorem finiteJacobiTransport_eq_jacobiCongruence
    {N : ℕ} (inverseGramFactor shifted : Matrix (Fin N) (Fin N) ℝ) :
    finiteJacobiTransport inverseGramFactor shifted =
      jacobiCongruence inverseGramFactor shifted :=
  rfl

/-- Positive semidefiniteness survives the exact Jacobi congruence. -/
theorem finiteJacobiTransport_posSemidef
    {N : ℕ} {inverseGramFactor shifted : Matrix (Fin N) (Fin N) ℝ}
    (hshifted : shifted.PosSemidef) :
    (finiteJacobiTransport inverseGramFactor shifted).PosSemidef := by
  rw [finiteJacobiTransport,
    ← Matrix.conjTranspose_eq_transpose_of_trivial inverseGramFactor]
  exact
    hshifted.mul_mul_conjTranspose_same inverseGramFactor

/-- Hence every transported finite Jacobi matrix is symmetric. -/
theorem finiteJacobiTransport_isSymm
    {N : ℕ} {inverseGramFactor shifted : Matrix (Fin N) (Fin N) ℝ}
    (hshifted : shifted.PosSemidef) :
    (finiteJacobiTransport inverseGramFactor shifted).IsSymm :=
  Matrix.isHermitian_iff_isSymm.mp
    (finiteJacobiTransport_posSemidef hshifted).isHermitian

/-- Strict positivity is preserved when the whitening factor acts
injectively. -/
theorem finiteJacobiTransport_posDef
    {N : ℕ} {inverseGramFactor shifted : Matrix (Fin N) (Fin N) ℝ}
    (hshifted : shifted.PosDef)
    (hinjective : Function.Injective inverseGramFactor.vecMul) :
    (finiteJacobiTransport inverseGramFactor shifted).PosDef := by
  rw [finiteJacobiTransport,
    ← Matrix.conjTranspose_eq_transpose_of_trivial inverseGramFactor]
  exact
    hshifted.mul_mul_conjTranspose_same hinjective

/-- Exact whitening already forces the whitening factor to act injectively.
Thus injectivity is not an independent numerical assumption once the Gram
identity has been proved. -/
theorem inverseFactor_vecMul_injective_of_whitening
    {N : ℕ} {inverseGramFactor gram : Matrix (Fin N) (Fin N) ℝ}
    (hwhite : finiteJacobiTransport inverseGramFactor gram = 1) :
    Function.Injective inverseGramFactor.vecMul := by
  intro x y hxy
  have htransport := congrArg
    (fun z => Matrix.vecMul (Matrix.vecMul z gram)
      inverseGramFactor.transpose) hxy
  calc
    x = Matrix.vecMul x (1 : Matrix (Fin N) (Fin N) ℝ) := by simp
    _ = Matrix.vecMul x
        (finiteJacobiTransport inverseGramFactor gram) := by rw [hwhite]
    _ = Matrix.vecMul
        (Matrix.vecMul (Matrix.vecMul x inverseGramFactor) gram)
        inverseGramFactor.transpose := by
      simp [finiteJacobiTransport, Matrix.vecMul_vecMul]
    _ = Matrix.vecMul
        (Matrix.vecMul (Matrix.vecMul y inverseGramFactor) gram)
        inverseGramFactor.transpose := htransport
    _ = Matrix.vecMul y
        (finiteJacobiTransport inverseGramFactor gram) := by
      simp [finiteJacobiTransport, Matrix.vecMul_vecMul]
    _ = Matrix.vecMul y (1 : Matrix (Fin N) (Fin N) ℝ) := by rw [hwhite]
    _ = y := by simp

/-- Finite whitening data.  In the reference implementation
`inverseFactor = (cholesky G_N)⁻¹`; the defining property below is the exact
property of that choice used by the Jacobi step. -/
structure FiniteGramWhitening (moments : ℕ → ℝ) (N : ℕ) where
  inverseFactor : Matrix (Fin N) (Fin N) ℝ
  gram_identity :
    finiteJacobiTransport inverseFactor (hankelGram moments N) = 1
  inverseFactor_vecMul_injective : Function.Injective inverseFactor.vecMul

/-- Build the finite whitening package from its defining exact identity. -/
def FiniteGramWhitening.ofIdentity
    (moments : ℕ → ℝ) (N : ℕ)
    (inverseFactor : Matrix (Fin N) (Fin N) ℝ)
    (hwhite :
      finiteJacobiTransport inverseFactor (hankelGram moments N) = 1) :
    FiniteGramWhitening moments N where
  inverseFactor := inverseFactor
  gram_identity := hwhite
  inverseFactor_vecMul_injective :=
    inverseFactor_vecMul_injective_of_whitening hwhite

/-- The finite Jacobi matrix constructed from one moment sequence. -/
def finiteJacobiSection
    (moments : ℕ → ℝ) (N : ℕ)
    (whitening : FiniteGramWhitening moments N) :
    Matrix (Fin N) (Fin N) ℝ :=
  finiteJacobiTransport whitening.inverseFactor (shiftedHankel moments N)

/-- The whitening stored in the construction normalizes the unshifted Hankel
Gram matrix exactly. -/
theorem finiteGramWhitening_identity
    (moments : ℕ → ℝ) (N : ℕ)
    (whitening : FiniteGramWhitening moments N) :
    finiteJacobiTransport whitening.inverseFactor (hankelGram moments N) = 1 :=
  whitening.gram_identity

/-- A shifted Gram realization makes the native finite Jacobi section
positive semidefinite at every selected order and for every exact whitening. -/
theorem finiteJacobiSection_posSemidef_of_shiftedGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (whitening : FiniteGramWhitening moments N) :
    (finiteJacobiSection moments N whitening).PosSemidef := by
  exact finiteJacobiTransport_posSemidef
    (shiftedHankel_posSemidef_of_gramRepresentation hrep N)

/-- If the shifted features are linearly independent, the native finite
Jacobi section is positive definite. -/
theorem finiteJacobiSection_posDef_of_shiftedGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (whitening : FiniteGramWhitening moments N)
    (hli : LinearIndependent ℝ (fun i : Fin N ↦ feature (i : ℕ))) :
    (finiteJacobiSection moments N whitening).PosDef := by
  exact finiteJacobiTransport_posDef
    (shiftedHankel_posDef_of_gramRepresentation hrep N hli)
    whitening.inverseFactor_vecMul_injective

/-- In particular, the native finite Jacobi section is symmetric. -/
theorem finiteJacobiSection_isSymm_of_shiftedGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation moments feature)
    (N : ℕ) (whitening : FiniteGramWhitening moments N) :
    (finiteJacobiSection moments N whitening).IsSymm :=
  Matrix.isHermitian_iff_isSymm.mp
    (finiteJacobiSection_posSemidef_of_shiftedGram hrep N whitening).isHermitian

end

end GeometryOfNumbers.Analysis
