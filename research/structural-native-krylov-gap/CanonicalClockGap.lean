import OddSourceBoxes
import GeometryOfNumbers.Analysis.MaterialClockKrylovGap
import GeometryOfNumbers.Analysis.BaseTwoCanonicalDressingMoments

/-! Native canonical source tests, reusing the already-certified theta boxes.
The physical complete signal is identified before its coefficient recurrence.
No source vector or moment is redefined to fit a Gram. -/
namespace CarryStructuralKrylov
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open GeometryOfNumbers.Analysis.NativeMaterialClock
open GeometryOfNumbers.Analysis.FiniteClockKrylov GeometryOfNumbers.Analysis.MaterialClockKrylovGap
open CarrySelfAdjointOperator CarryMaterialCanonicalComparison CarrySixthOdd CarryIntegralCertificate
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- Same full source, hence same real even coefficients, at every order. -/
theorem canonical_phi_eq_native (n : ℕ) :
    baseTwoCanonicalPhi n = completedNativeRealEvenCharacteristicCoefficient n := by
  rw [baseTwoCanonicalPhi_eq_normalizedEvenJet]
  have hf : baseTwoCanonicalResponse =
      fun t : ℝ => completedNativeOperatorCharacteristic (t : ℂ) := funext material_response
  rw [hf, iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal]
  rfl

/-- Equality is obtained from the actual synthesized response and uniqueness;
no Hankel sign or moment realization is used to identify the sequence. -/
theorem canonical_moments_eq_native :
    baseTwoCanonicalMomentSequence = canonicalCompletedNativeLogDerivativeMoment := by
  apply GeometryOfNumbers.Analysis.IsLogDerivativeMomentSequence.unique baseTwoCanonicalPhi_zero_ne_zero
    baseTwoCanonicalLogMoment_isSequence
  intro n
  simp_rw [canonical_phi_eq_native]
  simpa only [neg_mul] using canonicalCompletedNativeLogDerivativeMoment_real_recurrence n

/-- The original theta-source boxes already separate the two low orders by
more than the geometric material-clock gap. Only existing enclosures enter. -/
theorem native_two_lt_one_quarter :
    canonicalCompletedNativeLogDerivativeMoment 2 <
      canonicalCompletedNativeLogDerivativeMoment 1 / 4 := by
  have h1 := mem_compactMomentBox 1
  have h2 := mem_compactMomentBox 2
  norm_num [compactMomentBox, compactMomentTable, Box.Mem, intervalScale] at h1 h2
  linarith

theorem canonical_two_lt_one_quarter :
    baseTwoCanonicalMomentSequence 2 < baseTwoCanonicalMomentSequence 1 / 4 := by
  rw [canonical_moments_eq_native]
  exact native_two_lt_one_quarter

/-- The original Taylor factorials do not repair the failure: the source
already lies below the corresponding 1/16 diagonal ruler. -/
theorem canonical_two_lt_one_sixteenth :
    baseTwoCanonicalMomentSequence 2 < baseTwoCanonicalMomentSequence 1 / 16 := by
  rw [canonical_moments_eq_native]
  have h1 := mem_compactMomentBox 1
  have h2 := mem_compactMomentBox 2
  norm_num [compactMomentBox, compactMomentTable, Box.Mem, intervalScale] at h1 h2
  linarith

/-- This uses the ORIGINAL normalized temporal jets, including 2!, without
changing amplitudes. The conflicting diagonals survive every unit phase. -/
theorem finite_normalized_jets_not_canonical_diagonals {M : ℕ}
    (v : FiniteRealSpectralHilbert M) :
    ¬ (‖GeometryOfNumbers.Analysis.FiniteClockJets.normalizedClockJet 1 v‖^2 =
        baseTwoCanonicalMomentSequence 1 ∧
      ‖GeometryOfNumbers.Analysis.FiniteClockJets.normalizedClockJet 2 v‖^2 =
        baseTwoCanonicalMomentSequence 2) := by
  rintro ⟨h1,h2⟩
  have hg := finite_normalized_jet_energy_gap v
  rw [h1,h2] at hg
  linarith [canonical_two_lt_one_sixteenth]

/-- No finite material source, at any cutoff, supplies the canonical first
column, even when its zeroth and first entries are allowed to be calibrated. -/
theorem finite_clock_not_canonical_firstColumn {M : ℕ}
    (v : FiniteRealSpectralHilbert M) :
    ¬ (∀ r : ℕ, baseTwoCanonicalMomentSequence r = finiteClockSpectralMoment v (2*r)) := by
  intro h
  have hg := finite_even_first_column_gap v
  rw [← h 1, ← h 2] at hg
  have hn := canonical_two_lt_one_quarter
  linarith

/-- In particular the canonical coefficient recurrence cannot hold for the
moments of the unchanged material clock and any supplied finite source. -/
theorem finite_clock_not_canonical_logDerivative_recurrence {M : ℕ}
    (v : FiniteRealSpectralHilbert M) :
    ¬ GeometryOfNumbers.Analysis.IsLogDerivativeMomentSequence baseTwoCanonicalPhi
      (fun r => finiteClockSpectralMoment v (2*r)) := by
  intro h
  have he := GeometryOfNumbers.Analysis.IsLogDerivativeMomentSequence.unique baseTwoCanonicalPhi_zero_ne_zero
    baseTwoCanonicalLogMoment_isSequence h
  exact finite_clock_not_canonical_firstColumn v (fun r => congrFun he r)

/-- Failure occurs already in the odd-zero and even-one diagonals of the
original parity Gram; it is not an extrapolation to high orders. -/
theorem finite_clock_not_canonical_parityGram {M : ℕ}
    (v : FiniteRealSpectralHilbert M) :
    ¬ IsParityMomentGramRepresentation baseTwoCanonicalMomentSequence (finiteClockParityKrylov v) := by
  intro h
  have own := finiteClockParityKrylov_gramRepresentation v
  have ho := (h (Sum.inr 0) (Sum.inr 0)).trans (own (Sum.inr 0) (Sum.inr 0)).symm
  have he := (h (Sum.inl 1) (Sum.inl 1)).trans (own (Sum.inl 1) (Sum.inl 1)).symm
  norm_num only [parityMomentKernel, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul] at ho he
  have hg := finite_even_first_column_gap v
  rw [← ho, ← he] at hg
  linarith [canonical_two_lt_one_quarter]

/-- The candidate already fails the exact H₆/K₆ regression entries.
No positivity of either block is used to manufacture a source. -/
theorem finite_clock_not_H6_K6 {M : ℕ} (v : FiniteRealSpectralHilbert M) :
    ¬ (GeometryOfNumbers.Analysis.hankelGram baseTwoCanonicalMomentSequence 6 =
        Matrix.gram ℝ (fun i : Fin 6 => finiteClockParityKrylov v (Sum.inl i.val)) ∧
      GeometryOfNumbers.Analysis.shiftedHankel baseTwoCanonicalMomentSequence 6 =
        Matrix.gram ℝ (fun i : Fin 6 => finiteClockParityKrylov v (Sum.inr i.val))) := by
  rintro ⟨he,ho⟩
  have h2 := congrFun (congrFun he (1 : Fin 6)) (1 : Fin 6)
  have h1 := congrFun (congrFun ho (0 : Fin 6)) (0 : Fin 6)
  have own := finiteClockParityKrylov_gramRepresentation v
  have e := own (Sum.inl 1) (Sum.inl 1)
  have o := own (Sum.inr 0) (Sum.inr 0)
  change baseTwoCanonicalMomentSequence 2 = _ at h2
  change baseTwoCanonicalMomentSequence 1 = _ at h1
  have heq : baseTwoCanonicalMomentSequence 2 = finiteClockSpectralMoment v 4 := by
    exact h2.trans e.symm
  have hoq : baseTwoCanonicalMomentSequence 1 = finiteClockSpectralMoment v 2 := by
    exact h1.trans o.symm
  have hg := finite_even_first_column_gap v
  rw [← hoq, ← heq] at hg
  linarith [canonical_two_lt_one_quarter]

/-- Infinite maximal material clock: only two applications need to exist.
All-order domains cannot repair the already-incompatible two energies. -/
theorem infinite_clock_not_canonical_diagonals :
    ¬ ∃ (v : infiniteRealSpectralGenerator.domain)
      (hv : infiniteRealSpectralGenerator v ∈ infiniteRealSpectralGenerator.domain),
      ‖infiniteRealSpectralGenerator v‖^2 = baseTwoCanonicalMomentSequence 1 ∧
      ‖infiniteRealSpectralGenerator ⟨infiniteRealSpectralGenerator v,hv⟩‖^2 =
        baseTwoCanonicalMomentSequence 2 :=
  infinite_clock_not_matching_two_diagonals _ _ canonical_two_lt_one_quarter

end
end CarryStructuralKrylov
