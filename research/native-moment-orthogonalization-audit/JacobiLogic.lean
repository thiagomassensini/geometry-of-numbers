import GeometryOfNumbers.Analysis.CanonicalFiniteHeight
import MomentFunctional

namespace NativeMomentOrthogonalization
open GeometryOfNumbers.Analysis
noncomputable section

/-- The symmetry hypothesis needed locally is symmetry, not semidefiniteness. -/
theorem transport_isSymm_of_isSymm {N : ℕ}
    (B K : Matrix (Fin N) (Fin N) ℝ) (hK : K.IsSymm) :
    (finiteJacobiTransport B K).IsSymm := by
  show (B * K * B.transpose).transpose = B * K * B.transpose
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hK.eq, Matrix.mul_assoc]

theorem shifted_transport_isSymm (h : ℕ → ℝ) (N : ℕ)
    (B : Matrix (Fin N) (Fin N) ℝ) :
    (finiteJacobiTransport B (shiftedHankel h N)).IsSymm :=
  transport_isSymm_of_isSymm B _ (shiftedHankel_isSymm h N)

theorem finiteJacobiSection_isSymm_unconditional (h : ℕ → ℝ) (N : ℕ)
    (w : FiniteGramWhitening h N) : (finiteJacobiSection h N w).IsSymm :=
  shifted_transport_isSymm h N w.inverseFactor

/-- A square exact whitening already entails invertibility. -/
theorem whitening_isUnit {N : ℕ} (B G : Matrix (Fin N) (Fin N) ℝ)
    (hw : finiteJacobiTransport B G = 1) : IsUnit B := by
  exact Matrix.vecMul_injective_iff_isUnit.mp
    (inverseFactor_vecMul_injective_of_whitening hw)

/-- The converse hidden in any claimed square real whitening. -/
theorem posDef_of_whitening {N : ℕ} (B G : Matrix (Fin N) (Fin N) ℝ)
    (hw : finiteJacobiTransport B G = 1) : G.PosDef := by
  have hb := whitening_isUnit B G hw
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff hb).mp
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  change (finiteJacobiTransport B G).PosDef
  rw [hw]
  exact Matrix.PosDef.one

theorem exists_whitening_iff_posDef {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) :
    (∃ B, finiteJacobiTransport B G = 1) ↔ G.PosDef := by
  constructor
  · rintro ⟨B, hw⟩
    exact posDef_of_whitening B G hw
  · intro hg
    exact ⟨canonicalLDLInverseFactor hg, canonicalLDLInverseFactor_whitens hg⟩

/-- Once G is whitened, strict positivity of J is exactly strict positivity
of K. A feature-family hypothesis is unnecessary for this local consumer. -/
theorem finiteJacobiSection_posDef_iff_shifted (h : ℕ → ℝ) (N : ℕ)
    (w : FiniteGramWhitening h N) :
    (finiteJacobiSection h N w).PosDef ↔ (shiftedHankel h N).PosDef := by
  have hb := whitening_isUnit w.inverseFactor _ w.gram_identity
  simpa [finiteJacobiSection, finiteJacobiTransport, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (x := shiftedHankel h N) hb)

/-- Same canonical J, directly from the two section certificates. -/
theorem canonicalSection_posDef_of_sections (h : ℕ → ℝ) (N : ℕ)
    (hG : (hankelGram h N).PosDef) (hK : (shiftedHankel h N).PosDef) :
    (canonicalFiniteJacobiSection h N hG).PosDef :=
  (finiteJacobiSection_posDef_iff_shifted h N (canonicalHankelWhitening h N hG)).mpr hK

/-- The original inverse-square-root formula without requiring an auxiliary
Gram feature package as input. No section sign is inferred here. -/
def canonicalHeightFromSections (h : ℕ → ℝ) (N : ℕ)
    (hG : (hankelGram h N).PosDef) (hK : (shiftedHankel h N).PosDef) :
    Matrix (Fin N) (Fin N) ℝ :=
  finiteHeightOperator (canonicalSection_posDef_of_sections h N hG hK)

/-- Exact equality to the existing height operator, not a replacement. -/
theorem canonicalHeightFromSections_eq_existing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {h : ℕ → ℝ} {feature : ℕ → E}
    (hrep : IsShiftedMomentGramRepresentation h feature)
    (N : ℕ) (hG : (hankelGram h N).PosDef)
    (hli : LinearIndependent ℝ (fun i : Fin N => feature i)) :
    canonicalHeightFromSections h N hG
      (shiftedHankel_posDef_of_gramRepresentation hrep N hli) =
      canonicalFiniteHeightOperator hrep N hG hli := rfl

end
end NativeMomentOrthogonalization
