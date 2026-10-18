import OddTrialPositivity
import TenSourceReturn

/-! Physical transport starts AFTER both genuine 6x6 sectors are positive.
Every source transform, corrected port and physical carrier is inherited. -/
namespace CarrySixthOdd
open CarryThetaPattern CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCriticalSource CarryCorrectedGreenPorts CarryReturnCompatibility
open GeometryOfNumbers.Analysis CarryMaterialMixedSchurComparison Filter
open scoped BigOperators Matrix ComplexConjugate InnerProductSpace Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem twelve_boundary_positive (x : Fin 12 → ℂ) (hx : x ≠ 0) :
    0 < nativeSourceFiniteBoundaryEnergy 12 x :=
  (finiteBoundary_positive_iff_sectorMatrices 6).mpr
    ⟨CarrySixthEven.even_source_six_posDef,odd_source_six_posDef⟩ x hx

theorem twelve_return_eventually_contractive :
    ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k 12‖ ≤ 1 := by
  obtain ⟨ε,hε,hb⟩ := (nativeSourceFiniteBoundaryEnergy_pos_iff_margin 12).mp twelve_boundary_positive
  exact radialReturnTransfer_even_eventually_norm_le_one_of_boundary_margin 6 ε hε hb

theorem return_contractive_through_twelve (N : ℕ) (hN : N ≤ 12) :
    ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k N‖ ≤ 1 := by
  filter_upwards [twelve_return_eventually_contractive] with k hk
  exact radialReturnTransfer_norm_le_one_of_prefix k hN hk

theorem correctedGreen_twelve_physical_realization (eta : ℝ) (heta : eta ≠ 0) :
    ∃ v : Fin 12 → CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ a, v a ∈ RadialIncidentSpan 0 12) ∧
      (∀ a b, inner ℂ (v a) (v b) = carryValveConfluentJet eta a.val b.val) :=
  correctedGreen_realization_of_contractive 11 twelve_return_eventually_contractive eta heta

theorem canonical_twelve_physical_realization :
    ∃ v : Fin 12 → CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ a, v a ∈ RadialIncidentSpan 0 12) ∧
      (∀ a b, inner ℂ (fullSourceJet v a) (fullSourceJet v b) =
        polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment a.val b.val) := by
  obtain ⟨v,hmem,hv⟩ := correctedGreen_twelve_physical_realization 1 (by norm_num)
  refine ⟨v,hmem,?_⟩
  apply fullSourceJet_pairing v
  intro a b
  rw [hv a b,material_valve_confluent_jet 1 (by norm_num)]

theorem twelve_nested_physical_realization (eta : ℝ) (heta : eta ≠ 0) :
    ∃ v : Fin 12 → CanonicalCompletedNativeChiralCauchyCarrier,
      ∀ (N : ℕ) (hN : N ≤ 12) (a b : Fin N),
        inner ℂ (v (Fin.castLE hN a)) (v (Fin.castLE hN b)) =
          carryValveConfluentJet eta a.val b.val := by
  obtain ⟨v,_,hv⟩ := correctedGreen_twelve_physical_realization eta heta
  exact ⟨v,fun N hN a b => hv (Fin.castLE hN a) (Fin.castLE hN b)⟩


theorem ten_to_twelve_residual_crossings :
    ∀ᶠ k : ℕ in atTop, ∀ a b : Fin 10,
      inner ℂ (residualEnergyJet k 11 (Fin.castLE (by decide : 10 ≤ 12) a))
        (residualEnergyJet k 11 (Fin.castLE (by decide : 10 ≤ 12) b)) =
      inner ℂ (residualEnergyJet k 9 a) (residualEnergyJet k 9 b) := by
  filter_upwards [twelve_return_eventually_contractive] with k hk
  intro a b
  exact residualJets_prefix_pairing k (by decide : 9 ≤ 11) hk a b

/-- Arbitrary independent complex inputs are synthesized before pairing. -/
theorem correctedGreen_twelve_synthesis_pairing_tendsto
    (eta : ℝ) (heta : eta ≠ 0) (x y : Fin 12 → ℂ) :
    Tendsto (fun k => inner ℂ (residualEnergySynthesis k 11 x) (residualEnergySynthesis k 11 y))
      atTop (𝓝 (∑ a : Fin 12, ∑ b : Fin 12,
        conj (x a)*y b*carryValveConfluentJet eta a.val b.val)) := by
  simp_rw [material_valve_confluent_jet eta heta]
  exact residualEnergySynthesis_pairing_tendsto_of_contractive 11
    twelve_return_eventually_contractive x y

/-- ONE physical family realizes all pairs in all prefixes. No membership
in a smaller prefix carrier is asserted. -/
theorem canonical_twelve_nested_realization :
    ∃ v : Fin 12 → CanonicalCompletedNativeChiralCauchyCarrier,
      ∀ (N : ℕ) (hN : N ≤ 12) (a b : Fin N),
        inner ℂ (fullSourceJet v (Fin.castLE hN a))
          (fullSourceJet v (Fin.castLE hN b)) =
            polarizedGreenMomentCoefficient h a.val b.val := by
  obtain ⟨v,_,hv⟩ := canonical_twelve_physical_realization
  exact ⟨v,fun N hN a b => hv (Fin.castLE hN a) (Fin.castLE hN b)⟩

end
end CarrySixthOdd
