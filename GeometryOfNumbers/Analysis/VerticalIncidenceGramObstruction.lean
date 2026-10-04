import GeometryOfNumbers.Analysis.RealTfvdCenterLegMomentSeam

/-!
# Exact TFVD reconstruction does not identify a moment Gram

The full real fiber analysis, including its boundary, is synthesized before
reassembling the branch vector. It recovers the input. Any subsequent linear
isometry preserves its ordinary Gram, which cannot be a sum-index moment kernel.
This obstruction concerns only reconstructed coordinate incidences and their
isometric images. It says nothing against a different completed vector readout
or positivity of the canonical moment sequence.
-/
namespace GeometryOfNumbers.Analysis
noncomputable section
open scoped lp ENNReal

private def reconstructedCoordinate (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : GlobalC2BranchCarrier) (a : GlobalC2BranchAddress) : RealPlaneHilbert :=
  realPlaneHilbertEquiv
    ((c2FiberTfvdSynthesis eta h0.le h1 (c2FiberTfvdAnalysis eta x)
        a.1 a.2.1 0) a.2.2,
     (c2FiberTfvdSynthesis eta h0.le h1 (c2FiberTfvdAnalysis eta x)
        a.1 a.2.1 1) a.2.2)

private theorem reconstructedCoordinate_eq (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : GlobalC2BranchCarrier) (a : GlobalC2BranchAddress) :
    reconstructedCoordinate eta h0 h1 x a = x a := by
  unfold reconstructedCoordinate
  rw [c2FiberTfvdSynthesis_analysis eta h0 h1 x]
  change realPlaneHilbertEquiv (x a 0, x a 1) = x a
  exact realPlaneHilbertEquiv.apply_symm_apply (x a)

/-- Reassemble both synthesized real quadratures at every original address.
This is reconstruction of the input, not a completed/dressed moment observable. -/
def c2TfvdReconstructedBranchState (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : GlobalC2BranchCarrier) : GlobalC2BranchCarrier :=
  ⟨reconstructedCoordinate eta h0 h1 x, by
    have heq : reconstructedCoordinate eta h0 h1 x = x :=
      funext (reconstructedCoordinate_eq eta h0 h1 x)
    rw [heq]
    exact lp.memℓp x⟩

/-- Whole-vector equality precedes every inner product in this audit. -/
theorem c2TfvdReconstructedBranchState_eq (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x : GlobalC2BranchCarrier) : c2TfvdReconstructedBranchState eta h0 h1 x = x := by
  apply lp.ext
  exact funext (reconstructedCoordinate_eq eta h0 h1 x)

theorem c2TfvdReconstructedBranchState_inner (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (x y : GlobalC2BranchCarrier) :
    inner ℝ (c2TfvdReconstructedBranchState eta h0 h1 x)
      (c2TfvdReconstructedBranchState eta h0 h1 y) = inner ℝ x y := by
  rw [c2TfvdReconstructedBranchState_eq, c2TfvdReconstructedBranchState_eq]

/-- R2 reconstruction cannot change the incidence-basis no-go. -/
theorem c2TfvdReconstructedIncidence_not_parityMomentGram
    (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (moments : ℕ → ℝ) :
    ¬ IsParityMomentGramRepresentation moments
      (fun i => c2TfvdReconstructedBranchState eta h0 h1 (c2RealIncidenceJet i)) := by
  simpa only [c2TfvdReconstructedBranchState_eq] using
    c2RealIncidenceJet_not_parityMomentGram moments

section IsometricSynthesis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Includes any metric-preserving linear packaging of the reconstructed incidences. -/
theorem c2IsometricIncidenceSynthesis_inner (A : GlobalC2BranchCarrier →ₗᵢ[ℝ] E)
    (i j : ℕ ⊕ ℕ) :
    inner ℝ (A (c2RealIncidenceJet i)) (A (c2RealIncidenceJet j)) =
      if i = j then 1 else 0 := by
  rw [A.inner_map_map, c2RealIncidenceJet_inner]

/-- This family is independent even after an arbitrary real linear isometry. -/
theorem c2IsometricIncidenceSynthesis_linearIndependent
    (A : GlobalC2BranchCarrier →ₗᵢ[ℝ] E) :
    LinearIndependent ℝ (fun i => A (c2RealIncidenceJet i)) :=
  c2RealIncidenceJet_linearIndependent.map_injOn A.toLinearMap A.injective.injOn

/-- Its own finite Gram blocks are positive definite, at every order. This does
not identify either matrix with a Hankel section of the canonical moments. -/
theorem c2IsometricIncidenceSynthesis_gramPair_posDef
    (A : GlobalC2BranchCarrier →ₗᵢ[ℝ] E) (N : ℕ) :
    (Matrix.gram ℝ (fun i : Fin N => A (c2RealIncidenceJet (Sum.inl i.val)))).PosDef ∧
    (Matrix.gram ℝ (fun i : Fin N => A (c2RealIncidenceJet (Sum.inr i.val)))).PosDef := by
  have hi := c2IsometricIncidenceSynthesis_linearIndependent A
  exact ⟨Matrix.posDef_gram_of_linearIndependent
      ((hi.comp Sum.inl Sum.inl_injective).comp Fin.val Fin.val_injective),
    Matrix.posDef_gram_of_linearIndependent
      ((hi.comp Sum.inr Sum.inr_injective).comp Fin.val Fin.val_injective)⟩

/-- Already the order-three even block cannot be a Hankel matrix: the entries
(0,2) and (1,1) require the same moment to be respectively zero and one. -/
theorem c2IsometricIncidenceSynthesis_hankel_three_ne_gram
    (A : GlobalC2BranchCarrier →ₗᵢ[ℝ] E) (moments : ℕ → ℝ) :
    hankelGram moments 3 ≠
      Matrix.gram ℝ (fun i : Fin 3 => A (c2RealIncidenceJet (Sum.inl i.val))) := by
  intro h
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 2) h
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) h
  simp only [hankelGram, Matrix.gram, Matrix.of_apply,
    c2IsometricIncidenceSynthesis_inner] at h02 h11
  norm_num at h02 h11
  exact zero_ne_one (h02.symm.trans h11)

/-- Norm preservation and independence do not supply the missing moment readout. -/
theorem c2IsometricIncidenceSynthesis_not_parityMomentGram
    (A : GlobalC2BranchCarrier →ₗᵢ[ℝ] E) (moments : ℕ → ℝ) :
    ¬ IsParityMomentGramRepresentation moments (fun i => A (c2RealIncidenceJet i)) := by
  intro h
  apply c2RealIncidenceJet_not_parityMomentGram moments
  intro i j
  simpa only [Matrix.gram, Matrix.of_apply, A.inner_map_map] using h i j

/-- Canonical specialization of the representation-specific obstruction. -/
theorem c2IsometricIncidenceSynthesis_not_canonicalParityMomentGram
    (A : GlobalC2BranchCarrier →ₗᵢ[ℝ] E) :
    ¬ IsParityMomentGramRepresentation BaseTwoCompletion.baseTwoCanonicalMomentSequence
      (fun i => A (c2RealIncidenceJet i)) :=
  c2IsometricIncidenceSynthesis_not_parityMomentGram A _

end IsometricSynthesis
end
end GeometryOfNumbers.Analysis
