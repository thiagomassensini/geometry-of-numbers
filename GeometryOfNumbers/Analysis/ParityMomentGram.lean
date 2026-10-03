import GeometryOfNumbers.Analysis.MomentGramPositivity

/-!
# One parity Gram kernel and its Hankel sections

Neutral coefficient-level mathematics. A representation is a proposition,
not a construction of jets from moments and not a certificate for any source.
Concrete geometric identification must be proved independently.
-/
namespace GeometryOfNumbers.Analysis
noncomputable section

/-- The two parity blocks, with zero mixed entries. -/
def parityMomentKernel (moments : ℕ → ℝ) : Matrix (ℕ ⊕ ℕ) (ℕ ⊕ ℕ) ℝ
  | Sum.inl i, Sum.inl j => moments (i + j)
  | Sum.inr i, Sum.inr j => moments (i + j + 1)
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0

/-- One existing vector family realizes both blocks and their orthogonality. -/
def IsParityMomentGramRepresentation
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (moments : ℕ → ℝ) (jet : (ℕ ⊕ ℕ) → E) : Prop :=
  ∀ i j, parityMomentKernel moments i j = Matrix.gram ℝ jet i j

theorem parityMomentGram_even
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsParityMomentGramRepresentation moments jet) :
    IsMomentGramRepresentation moments (fun n => jet (Sum.inl n)) := by
  intro i j
  simpa [parityMomentKernel, Matrix.gram] using hrep (Sum.inl i) (Sum.inl j)

theorem parityMomentGram_odd
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsParityMomentGramRepresentation moments jet) :
    IsShiftedMomentGramRepresentation moments (fun n => jet (Sum.inr n)) := by
  intro i j
  simpa [parityMomentKernel, Matrix.gram] using hrep (Sum.inr i) (Sum.inr j)

theorem parityMomentGram_even_odd_orthogonal
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsParityMomentGramRepresentation moments jet) (i j : ℕ) :
    inner ℝ (jet (Sum.inl i)) (jet (Sum.inr j)) = 0 := by
  simpa [parityMomentKernel, Matrix.gram] using (hrep (Sum.inl i) (Sum.inr j)).symm

/-- Semidefinite positivity follows from the vector representation, at every order. -/
theorem hankelPair_posSemidef_of_parityMomentGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsParityMomentGramRepresentation moments jet) (N : ℕ) :
    (hankelGram moments N).PosSemidef ∧ (shiftedHankel moments N).PosSemidef :=
  ⟨hankelGram_posSemidef_of_gramRepresentation (parityMomentGram_even hrep) N,
   shiftedHankel_posSemidef_of_gramRepresentation (parityMomentGram_odd hrep) N⟩

/-- Strictness is separate: independence of both prefixes upgrades both sections. -/
theorem hankelPair_posDef_of_parityMomentGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {moments : ℕ → ℝ} {jet : (ℕ ⊕ ℕ) → E}
    (hrep : IsParityMomentGramRepresentation moments jet) (N : ℕ)
    (heven : LinearIndependent ℝ (fun i : Fin N => jet (Sum.inl (i : ℕ))))
    (hodd : LinearIndependent ℝ (fun i : Fin N => jet (Sum.inr (i : ℕ)))) :
    (hankelGram moments N).PosDef ∧ (shiftedHankel moments N).PosDef :=
  ⟨hankelGram_posDef_of_gramRepresentation (parityMomentGram_even hrep) N heven,
   shiftedHankel_posDef_of_gramRepresentation (parityMomentGram_odd hrep) N hodd⟩

end
end GeometryOfNumbers.Analysis
