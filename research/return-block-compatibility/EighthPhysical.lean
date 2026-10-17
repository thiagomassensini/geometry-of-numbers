import EighthReturnCheck
import JetCompatibility

namespace CarryReturnCompatibility
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open GeometryOfNumbers.Analysis CarryCorrectedGreenPorts
open CarryMaterialMixedSchurComparison
open Filter
open scoped InnerProductSpace Topology
noncomputable section
set_option autoImplicit false

theorem return_eventually_contractive_through_eight (N : ℕ) (hN : N ≤ 8) :
    ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1 := by
  filter_upwards [eighthReturn_eventually_contractive] with k hk
  exact radialReturnTransfer_norm_le_one_of_prefix k hN hk

/-- New physical block 0..7, from the actual source return estimate. -/
theorem correctedGreen_eight_physical_realization (eta : ℝ) (heta : eta ≠ 0) :
    ∃ v : Fin 8 → CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ a, v a ∈ RadialIncidentSpan 0 8) ∧
      (∀ a b, inner ℂ (v a) (v b) = carryValveConfluentJet eta a.val b.val) :=
  correctedGreen_realization_of_contractive 7 eighthReturn_eventually_contractive eta heta

theorem canonical_eight_physical_realization :
    ∃ v : Fin 8 → CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ a, v a ∈ RadialIncidentSpan 0 8) ∧
      (∀ a b, inner ℂ (fullSourceJet v a) (fullSourceJet v b) =
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment a.val b.val) := by
  obtain ⟨v,hmem,hv⟩ := correctedGreen_eight_physical_realization 1 (by norm_num)
  refine ⟨v,hmem,?_⟩
  apply fullSourceJet_pairing v
  intro a b
  rw [hv a b, material_valve_confluent_jet 1 (by norm_num)]

/-- One eight-source physical family already gives compatible restrictions
for ALL its prefixes. The seven-source realization need not be chosen again. -/
theorem correctedGreen_eight_nested_realization (eta : ℝ) (heta : eta ≠ 0) :
    ∃ v : Fin 8 → CanonicalCompletedNativeChiralCauchyCarrier,
      ∀ (N : ℕ) (hN : N ≤ 8) (a b : Fin N),
        inner ℂ (v (Fin.castLE hN a)) (v (Fin.castLE hN b)) =
          carryValveConfluentJet eta a.val b.val := by
  obtain ⟨v,_,hv⟩ := correctedGreen_eight_physical_realization eta heta
  exact ⟨v,fun N hN a b => hv (Fin.castLE hN a) (Fin.castLE hN b)⟩

/-- Source-derived transition is available eventually for any two prefixes
inside the eight-source block. There is ONE common cutoff for these finitely
many prefixes, furnished by the bound on the actual largest return. -/
theorem residualJets_through_eight_eventually_compatible :
    ∀ᶠ k : ℕ in atTop, ∀ (N M : ℕ) (h : N ≤ M), M+1 ≤ 8 →
      ∃ hret : ‖radialReturnTransfer k (M+1)‖ ≤ 1,
        ∀ a : Fin (N+1),
          energyTransition k (Nat.add_le_add_right h 1) hret (residualJetImage k N a) =
            residualJetImage k M (Fin.castLE (Nat.add_le_add_right h 1) a) := by
  filter_upwards [eighthReturn_eventually_contractive] with k hk
  intro N M h hM
  exact ⟨radialReturnTransfer_norm_le_one_of_prefix k hM hk,
    fun a => residualJetImage_transition k h _ a⟩

end
end CarryReturnCompatibility
