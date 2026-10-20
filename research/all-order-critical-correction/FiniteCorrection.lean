import PairCorrection

namespace CarryAllOrderCorrection
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarrySourceLaw Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- The SAME full physical source in its inherited parity chart. No moment
or target Gram is used to define the physical jet vectors. -/
theorem synthesis_parity (s : Fin 2) (N k : ℕ) (v : Fin N → ℝ) :
    nativeSourceProjectiveBoundaryJetSynthesis N k (parityCoordinates s v) =
      ∑ i : Fin N, (v i:ℂ) • projectiveChiralDifferenceJet k (2*i.val+s.val) := by
  change (∑ i : Fin N ⊕ Fin N,
    Sum.elim (nativeSourceEvenBoundaryPhase N (parityCoordinates s v))
      (nativeSourceOddBoundaryPhase N (parityCoordinates s v)) i •
      projectiveChiralDifferenceJet k
        (Sum.elim (fun i : Fin N => 2*i.val) (fun i : Fin N => 2*i.val+1) i)) = _
  rw [Fintype.sum_sum_type]
  fin_cases s
  all_goals simp [parityCoordinates,nativeSourceEvenBoundaryPhase_fromParity,
    nativeSourceOddBoundaryPhase_fromParity]

def parityPairing (s : Fin 2) (N : ℕ) (v w : Fin N → ℝ) (k : ℕ) : ℂ :=
  canonicalCompletedNativeProjectiveChiralForm
    (nativeSourceProjectiveBoundaryJetSynthesis N k (parityCoordinates s v))
    (nativeSourceProjectiveBoundaryJetSynthesis N k (parityCoordinates s w))

def boundaryPairing (s N : ℕ) (v w : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, v i*w j*canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+s)

def boundaryCorrection (s N : ℕ) (v w : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, v i*w j*(canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+s+1)*
    correctionWeight (2*i.val+s) (2*j.val+s))

/-- Two independent complete syntheses, before taking a diagonal. All
ordered crosses of the original pair of source channels remain explicit. -/
theorem parityPairing_eq_sum (s : Fin 2) (N k : ℕ) (v w : Fin N → ℝ) :
    parityPairing s N v w k = ∑ i : Fin N, ∑ j : Fin N,
      (v i:ℂ)*(w j:ℂ)*canonicalCompletedNativeProjectiveChiralForm
        (projectiveChiralDifferenceJet k (2*i.val+s.val))
        (projectiveChiralDifferenceJet k (2*j.val+s.val)) := by
  unfold parityPairing
  rw [nativeSourceProjectiveBoundaryJetSynthesis_pairing]
  change (∑ i : Fin N ⊕ Fin N, ∑ j : Fin N ⊕ Fin N,
    conj (Sum.elim (nativeSourceEvenBoundaryPhase N (parityCoordinates s v))
      (nativeSourceOddBoundaryPhase N (parityCoordinates s v)) i) *
    Sum.elim (nativeSourceEvenBoundaryPhase N (parityCoordinates s w))
      (nativeSourceOddBoundaryPhase N (parityCoordinates s w)) j *
    canonicalCompletedNativeProjectiveChiralForm
      (projectiveChiralDifferenceJet k
        (Sum.elim (fun i : Fin N => 2*i.val) (fun i : Fin N => 2*i.val+1) i))
      (projectiveChiralDifferenceJet k
        (Sum.elim (fun i : Fin N => 2*i.val) (fun i : Fin N => 2*i.val+1) j))) = _
  fin_cases s
  all_goals simp [parityCoordinates,Fintype.sum_sum_type,
    nativeSourceEvenBoundaryPhase_fromParity,nativeSourceOddBoundaryPhase_fromParity]

/-- Arbitrary finite dimension, independent real inputs, BOTH source
channels and every ordered cross. No sign or invertibility hypothesis. -/
theorem finite_polarized_second_correction (s : Fin 2) (N : ℕ) (v w : Fin N → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℂ)+1)^2 *
      (parityPairing s N v w k-(boundaryPairing s.val N v w:ℂ))) atTop
      (nhds (boundaryCorrection s.val N v w:ℂ)) := by
  have hs := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      (projective_pairing_second_correction i.val j.val s.val).const_mul
        ((v i:ℂ)*(w j:ℂ))))
  have hc : (∑ i : Fin N, ∑ j : Fin N,
      (v i:ℂ)*(w j:ℂ)*((canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+s.val+1)*
        correctionWeight (2*i.val+s.val) (2*j.val+s.val):ℝ):ℂ)) =
      (boundaryCorrection s.val N v w:ℂ) := by
    simp only [boundaryCorrection,Complex.ofReal_sum,Complex.ofReal_mul]
  rw [hc] at hs
  apply hs.congr'
  filter_upwards with k
  rw [parityPairing_eq_sum]
  simp only [boundaryPairing,Complex.ofReal_sum,Complex.ofReal_mul,
    Finset.mul_sum,mul_sub,Finset.sum_sub_distrib]
  apply congrArg₂ (fun a b : ℂ => a-b)
  all_goals
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Original storage is twice the real readout of the already completely
synthesized signed projective form. This normalization is inherited. -/
theorem storage_eq_twice_pairing (s : Fin 2) (N k : ℕ) (v : Fin N → ℝ) :
    (storage k (nativeSourceChiralJetInput N k (parityCoordinates s v)) 1).re =
      2*(parityPairing s N v v k).re := by
  have he := nativeSourceProjectiveBoundaryJetSynthesis_energy N k (parityCoordinates s v)
  have hs := nativeSourceProjectiveBoundaryJetSynthesis_energy_eq_storage N k (parityCoordinates s v)
  change _ = 2*(canonicalCompletedNativeProjectiveChiralForm _ _).re
  linarith

/-- The next-step target of PR #44: a second-order rate for the ORIGINAL
finite Carry source in EVERY dimension and in both canonical parity sectors.
The coefficient has no assumed sign. -/
theorem finite_balance_second_correction (s : Fin 2) (N : ℕ) (v : Fin N → ℝ) :
    Tendsto (fun k : ℕ => ((k:ℝ)+1)^2 *
      ((storage k (nativeSourceChiralJetInput N k (parityCoordinates s v)) 1).re -
        2*boundaryPairing s.val N v v)) atTop
      (nhds (canonicalCorrection s.val N v)) := by
  have ht := (Complex.continuous_re.continuousAt.tendsto.comp
    (finite_polarized_second_correction s N v v)).const_mul (2:ℝ)
  have he : 2*boundaryCorrection s.val N v v = canonicalCorrection s.val N v := by
    unfold boundaryCorrection canonicalCorrection
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [Function.comp_def,Complex.ofReal_re] at ht
  rw [he] at ht
  apply ht.congr'
  filter_upwards with k
  rw [storage_eq_twice_pairing]
  norm_num [Complex.mul_re,Complex.mul_im,pow_two,Complex.sub_re]
  ring

end
end CarryAllOrderCorrection
