import GeometryOfNumbers.Analysis.ParityMomentGram
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Sum-index Hankel kernels from symmetric Krylov families

All operators here are total linear endomorphisms. In particular the finite
material clock has no domain obstruction. This lemma does not apply powers of
an unbounded operator outside its domain. A spectral moment is defined from an
independently supplied operator and vector, never the converse.
-/
namespace GeometryOfNumbers.Analysis
noncomputable section

section RCLike
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Symmetry moves all left powers to the right. Complex orientation is exact:
the inner product is conjugate-linear in its first argument. -/
theorem symmetricKrylov_inner_add (L : Module.End 𝕜 E) (hL : L.IsSymmetric)
    (v : E) (i j : ℕ) :
    inner 𝕜 ((L ^ i) v) ((L ^ j) v) = inner 𝕜 v ((L ^ (i + j)) v) := by
  rw [(hL.pow i) v ((L ^ j) v), pow_add]
  rfl

end RCLike

section Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Spectral sequence of an existing real vector and total operator. -/
def krylovSpectralMoment (L : Module.End ℝ E) (v : E) (r : ℕ) : ℝ :=
  inner ℝ v ((L ^ r) v)

/-- A symmetric Krylov family realizes its own sum-index moment sequence. -/
theorem krylovSpectralMoment_gramRepresentation (L : Module.End ℝ E)
    (hL : L.IsSymmetric) (v : E) :
    IsMomentGramRepresentation (krylovSpectralMoment L v) (fun r => (L ^ r) v) := by
  intro i j
  exact (symmetricKrylov_inner_add L hL v i j).symm

/-- One independently proved first-column identity propagates to the full
kernel. This is a generic implication, not an assumed canonical readout. -/
theorem firstColumn_of_symmetric_implies_hankelGram (L : Module.End ℝ E)
    (hL : L.IsSymmetric) (v : E) (moments : ℕ → ℝ)
    (hfirst : ∀ r, moments r = inner ℝ v ((L ^ r) v)) :
    IsMomentGramRepresentation moments (fun r => (L ^ r) v) := by
  intro i j
  rw [hfirst]
  exact (symmetricKrylov_inner_add L hL v i j).symm

theorem krylovSpectralMoment_hankel_posSemidef (L : Module.End ℝ E)
    (hL : L.IsSymmetric) (v : E) (N : ℕ) :
    (hankelGram (krylovSpectralMoment L v) N).PosSemidef :=
  hankelGram_posSemidef_of_gramRepresentation
    (krylovSpectralMoment_gramRepresentation L hL v) N

/-- Strictness still needs independent powers of this very vector. -/
theorem krylovSpectralMoment_hankel_posDef (L : Module.End ℝ E)
    (hL : L.IsSymmetric) (v : E) (N : ℕ)
    (hli : LinearIndependent ℝ (fun i : Fin N => (L ^ i.val) v)) :
    (hankelGram (krylovSpectralMoment L v) N).PosDef :=
  hankelGram_posDef_of_gramRepresentation
    (krylovSpectralMoment_gramRepresentation L hL v) N hli

/-- Log-derivative uniqueness can be used only AFTER an independent proof of
its coefficient relation for the proposed spectral sequence. -/
theorem krylovSpectralMoment_eq_of_logDerivativeRelations (L : Module.End ℝ E)
    (v : E) (phi moments : ℕ → ℝ) (hphi : phi 0 ≠ 0)
    (hcanonical : IsLogDerivativeMomentSequence phi moments)
    (hspectral : IsLogDerivativeMomentSequence phi (krylovSpectralMoment L v)) :
    moments = krylovSpectralMoment L v :=
  hcanonical.unique hphi hspectral

end Real
end
end GeometryOfNumbers.Analysis
