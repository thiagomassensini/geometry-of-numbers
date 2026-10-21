import OverlapGeometry
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport

/-! Pull back BOTH correction channels through the existing geometric jet
input. No coefficient, physical metric or normalization is selected from h. -/
namespace CarryJetOverlap
open CarrySelfAdjointOperator CarryFiberTransport ChiralReturn CPFormal.Analytic.Cp
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology
noncomputable section
set_option autoImplicit false

abbrev strip (k N : ℕ) := ∀ i : Fin N,
  operatorHeightParameter (radialPoint k i) ∈ genuineCriticalStrip

/-- The original source weight at internal radius one. -/
def sourceWeight (k : ℕ) {N : ℕ} (c : Fin N → ℂ) (i : Fin N) : ℂ :=
  c i/completedNativePositiveHermiteBiehlerCoordinate (radialPoint k i)

/-- Variable-parameter consumer defect, after the original Cauchy pairing. -/
def variableDefect (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (hs : strip k N) : ℂ :=
  ∑ i, ∑ j, conj (sourceWeight k c i)*sourceWeight k d j*
    (inner ℂ (radialField k i) (radialField k j)*
      defectPair (radialPoint k i) (radialPoint k j)
        (nativeSource (radialPoint k i) (hs i)) (nativeSource (radialPoint k j) (hs j)))

/-- Full off-diagonal overlap correction; no diagonal replacement is made. -/
def overlapCorrection (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (hs : strip k N) : ℂ :=
  ∑ i, ∑ j, conj (sourceWeight k c i)*sourceWeight k d j*
    ((1-radialOverlap k i j)*inner ℂ
      (ambientReadout (fiberPart (nativeSource (radialPoint k i) (hs i))))
      (ambientReadout (fiberPart (nativeSource (radialPoint k j) (hs j)))))

/-- The old four-channel object is split without dropping any crossing. -/
theorem four_channel_split (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (hs : strip k N) :
    coisometricFourChannelBalance k c d 1 1 (fun i => (hs i).1)=
      -Complex.I*variableDefect k c d hs+Complex.I*overlapCorrection k c d hs := by
  have h := finite_radial_overlap_transport k (sourceWeight k c) (sourceWeight k d) hs hs
  change coisometricFourChannelBalance k c d 1 1 (fun i => (hs i).1)=_
  unfold coisometricFourChannelBalance
  simp only [Complex.ofReal_one,one_pow,mul_one]
  change (∑ i, ∑ j, conj (sourceWeight k c i)*sourceWeight k d j*
    inner ℂ (radialField k i) (radialField k j)*_)=_
  simp_rw [mul_assoc] at h ⊢
  rw [h]
  unfold variableDefect overlapCorrection
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Two independently synthesized source vectors, with the coupled budget. -/
theorem source_balance_budget (k : ℕ) {N : ℕ} (c d : Fin N → ℂ) (hs : strip k N) :
    polarizedSourceBalance k c d 1 1=
      2*(inner ℂ (coisometricSourceSynthesis k c 1 (fun i => (hs i).1))
          (coisometricSourceSynthesis k d 1 (fun i => (hs i).1))+
        variableDefect k c d hs-overlapCorrection k c d hs) := by
  rw [polarizedSourceBalance_eq_coisometricGram_add_fourChannelBalance 0 k c d 1 1 hs,
    four_channel_split k c d hs]
  ring_nf
  simp [Complex.I_sq,sub_eq_add_neg]

/-- Exact signed pairing of the ORIGINAL whole jets, before signs or limits. -/
theorem jet_pairing_source_balance (n k : ℕ) (x y : Fin (2*n) → ℂ)
    (hp : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate
      (radialPoint k i) ≠ 0) :
    canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k y)=
      (2 : ℂ)⁻¹*polarizedSourceBalance k (nativeSourceChiralJetInput n k x)
        (nativeSourceChiralJetInput n k y) 1 1 := by
  have h := radialReturnTransfer_polarized_balance k (2*n)
    (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y) hp
  rw [radialReturnTransfer_exact,radialReturnTransfer_exact] at h
  change inner ℂ (radialIncidentSynthesis k (2*n) (nativeSourceChiralJetInput n k x))
      (radialIncidentSynthesis k (2*n) (nativeSourceChiralJetInput n k y))-
    inner ℂ (radialReturnedSynthesis k (2*n) (nativeSourceChiralJetInput n k x))
      (radialReturnedSynthesis k (2*n) (nativeSourceChiralJetInput n k y))=_ at h
  rw [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,
    nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource]
  unfold canonicalCompletedNativeProjectiveChiralForm
  exact congrArg (fun z : ℂ => (2 : ℂ)⁻¹*z) h

/-- Bookkeeping of the three old terms in the SAME native jet coordinates. -/
def jetBudget (n k : ℕ) (x y : Fin (2*n) → ℂ) (hs : strip k (2*n)) : ℂ :=
  inner ℂ
    (coisometricSourceSynthesis k (nativeSourceChiralJetInput n k x) 1 (fun i => (hs i).1))
    (coisometricSourceSynthesis k (nativeSourceChiralJetInput n k y) 1 (fun i => (hs i).1))+
  variableDefect k (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y) hs-
  overlapCorrection k (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y) hs

theorem jetBudget_eq_original_pairing (n k : ℕ) (x y : Fin (2*n) → ℂ)
    (hs : strip k (2*n))
    (hp : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate
      (radialPoint k i) ≠ 0) :
    jetBudget n k x y hs=canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k x)
      (nativeSourceProjectiveBoundaryJetSynthesis n k y) := by
  rw [jet_pairing_source_balance n k x y hp,
    source_balance_budget k (nativeSourceChiralJetInput n k x) (nativeSourceChiralJetInput n k y) hs]
  unfold jetBudget
  ring

theorem jetBudget_energy (n k : ℕ) (x : Fin (2*n) → ℂ) (hs : strip k (2*n))
    (hp : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate
      (radialPoint k i) ≠ 0) :
    4*(jetBudget n k x x hs).re=
      2*(‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).1‖^2-
        ‖(nativeSourceProjectiveBoundaryJetSynthesis n k x).2‖^2) := by
  rw [jetBudget_eq_original_pairing n k x x hs hp]
  exact nativeSourceProjectiveBoundaryJetSynthesis_energy n k x

/-- Polarized canonical limit on its physical domain, without choosing a
source outside the strip merely to state a totalized limit function. -/
theorem jetBudget_eventually_close (n : ℕ) (x y : Fin (2*n) → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ hs : strip k (2*n),
      dist (jetBudget n k x y hs)
        ((∑ i : Fin n, ∑ j : Fin n,
          conj (nativeSourceEvenBoundaryPhase n x i)*nativeSourceEvenBoundaryPhase n y j*
            (primeDepthGeometricMoment (i.val+j.val) : ℂ))+
         ∑ i : Fin n, ∑ j : Fin n,
          conj (nativeSourceOddBoundaryPhase n x i)*nativeSourceOddBoundaryPhase n y j*
            (primeDepthGeometricMoment (i.val+j.val+1) : ℂ)) < ε := by
  have h := Metric.tendsto_nhds.mp
    (nativeSourceProjectiveBoundaryJetSynthesis_pairing_tendsto n x y) ε hε
  filter_upwards [h,canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n)]
    with k hk hreg
  intro hs
  rw [jetBudget_eq_original_pairing n k x y hs (fun i => (hreg i).2.2)]
  exact hk

/-- Uniform in all coefficients for EACH fixed finite order. This is an
absolute error estimate for the signed budget, not a lower bound on it. -/
theorem jetBudget_eventually_energy_control (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∀ hs : strip k (2*n), ∀ x : Fin (2*n) → ℂ,
      |4*(jetBudget n k x x hs).re-nativeSourceFiniteBoundaryEnergy (2*n) x| ≤ η*‖x‖^2 := by
  filter_upwards [nativeSourceProjectiveBoundaryJetSynthesis_eventually_energy_control n η hη,
    canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n)] with k hk hreg
  intro hs x
  rw [jetBudget_energy n k x hs (fun i => (hreg i).2.2)]
  exact hk x

end
end CarryJetOverlap
