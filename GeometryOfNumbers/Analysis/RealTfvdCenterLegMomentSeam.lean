import GeometryOfNumbers.Analysis.C2RealFiberTfvdIncidence
import GeometryOfNumbers.Analysis.BaseTwoCanonicalDressingMoments

/-!
# The real completed center–leg readout gate

A typed target, not a premise used to certify the canonical moments. Exact TFVD
reconstruction and independence do not turn a coordinate incidence basis into
completed moment jets. The representation-specific obstruction below makes
that distinction explicit; it is not a no-go for a completed readout.
-/
namespace GeometryOfNumbers.Analysis
noncomputable section
open scoped lp ENNReal

/-- A completed vector readout must match the real polarized coefficient.
The vectors are inputs to the proposition, never constructed from moments. -/
def HasC2RealTfvdCenterLegReadout (moments : ℕ → ℝ)
    (jet : (ℕ ⊕ ℕ) → GlobalC2BranchCarrier) : Prop :=
  ∀ i j, c2ParityIncidenceCenter i ≠ (c2ParityIncidenceLeg j : ℕ) →
    polarizedRealMomentCoefficient moments (parityJetNumber i) (parityJetNumber j) =
      inner ℝ (jet i) (jet j)

/-- Canonical specialization remains a target, without an assumed vector dressing. -/
abbrev HasBaseTwoCanonicalTfvdCenterLegReadout
    (jet : (ℕ ⊕ ℕ) → GlobalC2BranchCarrier) : Prop :=
  HasC2RealTfvdCenterLegReadout BaseTwoCompletion.baseTwoCanonicalMomentSequence jet

theorem c2RealTfvdCenterLegReadout_iff_parityGram (moments : ℕ → ℝ)
    (jet : (ℕ ⊕ ℕ) → GlobalC2BranchCarrier) :
    HasC2RealTfvdCenterLegReadout moments jet ↔
      IsParityMomentGramRepresentation moments jet := by
  constructor
  · intro h i j
    simpa only [polarizedRealMomentCoefficient_eq_parityMomentKernel, Matrix.gram, Matrix.of_apply] using
      h i j (c2ParityIncidence_center_ne_leg i j)
  · intro h i j _
    simpa only [polarizedRealMomentCoefficient_eq_parityMomentKernel, Matrix.gram, Matrix.of_apply] using h i j

/-- Ordinary reconstructed incidence inner product; no canonical-moment assertion. -/
theorem c2RealIncidenceJet_inner (i j : ℕ ⊕ ℕ) :
    inner ℝ (c2RealIncidenceJet i) (c2RealIncidenceJet j) = if i = j then 1 else 0 := by
  unfold c2RealIncidenceJet
  rw [lp.inner_single_left]
  by_cases h : i = j
  · subst j
    simp only [lp.single_apply, Pi.single_eq_same]
    rw [PiLp.inner_apply]
    norm_num [realPlaneHilbertEquiv, Fin.sum_univ_two]
  · have ha : c2ParityIncidenceAddress i ≠ c2ParityIncidenceAddress j :=
      fun hij => h (c2ParityIncidenceAddress_injective hij)
    simp [lp.single_apply, Pi.single_eq_of_ne ha, h]

/-- A coordinate basis cannot realize a sum-index Hankel kernel, for any sequence.
This excludes only the bare incidence candidate, not completed geometric jets. -/
theorem c2RealIncidenceJet_not_parityMomentGram (moments : ℕ → ℝ) :
    ¬ IsParityMomentGramRepresentation moments c2RealIncidenceJet := by
  intro h
  have h02 := h (Sum.inl 0) (Sum.inl 2)
  have h11 := h (Sum.inl 1) (Sum.inl 1)
  simp only [parityMomentKernel, Matrix.gram, Matrix.of_apply, c2RealIncidenceJet_inner] at h02 h11
  norm_num at h02 h11
  exact zero_ne_one (h02.symm.trans h11)

/-- The named residual is an audit object, not a vanishing hypothesis. -/
def baseTwoRealTfvdCenterLegResidual (jet : (ℕ ⊕ ℕ) → GlobalC2BranchCarrier)
    (i j : ℕ ⊕ ℕ) : ℝ :=
  polarizedRealMomentCoefficient BaseTwoCompletion.baseTwoCanonicalMomentSequence
      (parityJetNumber i) (parityJetNumber j) - inner ℝ (jet i) (jet j)

theorem baseTwoRealTfvdCenterLegResidual_zero_iff
    (jet : (ℕ ⊕ ℕ) → GlobalC2BranchCarrier) :
    (∀ i j, baseTwoRealTfvdCenterLegResidual jet i j = 0) ↔
      HasBaseTwoCanonicalTfvdCenterLegReadout jet := by
  constructor
  · intro h i j _
    exact sub_eq_zero.mp (h i j)
  · intro h i j
    exact sub_eq_zero.mpr (h i j (c2ParityIncidence_center_ne_leg i j))

/-- Faithful incidence reconstruction does not itself supply the completed readout. -/
theorem c2RealIncidenceJet_not_canonicalCenterLegReadout :
    ¬ HasBaseTwoCanonicalTfvdCenterLegReadout c2RealIncidenceJet := by
  intro h
  exact c2RealIncidenceJet_not_parityMomentGram _
    ((c2RealTfvdCenterLegReadout_iff_parityGram _ _).mp h)

theorem c2RealIncidenceJet_residual_not_all_zero :
    ¬ (∀ i j, baseTwoRealTfvdCenterLegResidual c2RealIncidenceJet i j = 0) := by
  intro h
  exact c2RealIncidenceJet_not_canonicalCenterLegReadout
    ((baseTwoRealTfvdCenterLegResidual_zero_iff _).mp h)

end
end GeometryOfNumbers.Analysis
