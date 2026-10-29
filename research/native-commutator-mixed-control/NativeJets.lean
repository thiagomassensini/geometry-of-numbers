import MixedReduction
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport

namespace CarryCommutatorControl
open CarrySelfAdjointOperator CarryNativeTfvd NativeLaguerre ChiralReturn
open Filter Topology
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Embed a finite source vector without changing its addresses or coefficients. -/
def finiteEmbedding {N : ℕ} (c : Fin N → ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset (Finset.range N) (fun j => if h : j < N then c ⟨j,h⟩ else 0) (by
    intro j hj
    by_contra hn
    have hjn : ¬ j < N := by simpa using hn
    exact hj (by rw [dif_neg hjn]))

theorem finite_embedding_apply {N : ℕ} (c : Fin N → ℂ) (j : ℕ) :
    finiteEmbedding c j = if h : j < N then c ⟨j,h⟩ else 0 := rfl

theorem finite_embedding_support {N : ℕ} (c : Fin N → ℂ) :
    (finiteEmbedding c).support ⊆ Finset.range N := Finsupp.support_onFinset_subset

theorem finite_embedding_weight {N : ℕ} (c : Fin N → ℂ) (w : ℕ → ℂ) :
    coefficientWeight w (finiteEmbedding c) = finiteEmbedding (fun j => w j.val*c j) := by
  ext j
  simp only [coefficient_weight_apply, finite_embedding_apply]
  split_ifs <;> simp

theorem finite_embedding_synthesis {N : ℕ} (c : Fin N → ℂ) :
    physicalCauchySynthesis (finiteEmbedding c) =
      ∑ j : Fin N, c j • completedNativeChiralCauchyFeature j.val := by
  classical
  unfold physicalCauchySynthesis
  rw [Finsupp.linearCombination_apply]
  unfold finiteEmbedding
  rw [Finsupp.sum_onFinset _ _ _ _ (by intro j _; exact zero_smul ℂ _)]
  have h := Fin.sum_univ_eq_sum_range
    (fun j => (if h : j < N then c ⟨j,h⟩ else 0) • completedNativeChiralCauchyFeature j) N
  rw [← h]
  apply Finset.sum_congr rfl; intro j _
  rw [dif_pos j.isLt]

/-- These are exactly the pre-amplitude forward-difference coefficients from
the existing jet matrix. No inverse amplitude or target moment is used. -/
def rawJetCoefficients (n k : ℕ) (v : Fin (2*n) → ℂ) : Fin (2*n) → ℂ :=
  fun r => ∑ a, nativeSourceJetOrderPhase a.val *
    (((a.val.factorial : ℂ)*canonicalCompletedC3RadialSecondStep k^a.val)⁻¹) *
      completedGreenForwardWeight a.val r.val * v a

theorem original_jet_input_factor (n k : ℕ) (v : Fin (2*n) → ℂ) (r : Fin (2*n)) :
    nativeSourceChiralJetInput n k v r = incidentWeight k r.val * rawJetCoefficients n k v r := by
  change (∑ a, nativeSourceChiralJetInputMatrix n k r a * v a) = _
  simp only [nativeSourceChiralJetInputMatrix,
    rawJetCoefficients, incidentWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  ring

/-- Whole-vector sewing to the ORIGINAL projective boundary jets, with A once. -/
theorem raw_jet_original_source (n k : ℕ) (v : Fin (2*n) → ℂ) :
    physicalCompletedFiniteSource k (finiteEmbedding (rawJetCoefficients n k v)) =
      nativeSourceProjectiveBoundaryJetSynthesis n k v := by
  have hv : nativeSourceChiralJetInput n k v =
      fun r => incidentWeight k r.val * rawJetCoefficients n k v r :=
    funext (original_jet_input_factor n k v)
  rw [completed_source_weighted_identity, finite_embedding_weight, finite_embedding_weight,
    finite_embedding_synthesis, finite_embedding_synthesis,
    nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource, hv]
  apply Prod.ext
  all_goals
    simp only [radialIncidentSynthesis, radialReturnedSynthesis,
      completedNativeRadialChiralMultiplierState, completedNativeRadialChiralCauchyState,
      Finset.smul_sum, smul_smul, returnedWeight]
    apply Finset.sum_congr rfl; intro j _
    congr 1
    ring

/-- The law reaches EVERY native jet order and all independent source tests,
including radial-dependent critical directions. No sign premise enters. -/
theorem native_jet_commutator_eventually_null (n : ℕ)
    (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    ∀ᶠ k : ℕ in atTop, ∀ v w : Fin (2*n) → ℂ,
      canonicalCompletedNativeProjectiveChiralForm
        (completedSourceParts eta h0 h1 k (finiteEmbedding (rawJetCoefficients n k v)) 2)
        (completedSourceParts eta h0 h1 k (finiteEmbedding (rawJetCoefficients n k w)) 2) = 0 := by
  filter_upwards [completed_commutator_eventually_null (2*n) eta h0 h1] with k hk
  intro v w
  exact hk _ _ (finite_embedding_support _) (finite_embedding_support _)

end
end CarryCommutatorControl
