import FiniteSynthesis
import Mathlib.Topology.MetricSpace.Sequences

/-! Compactness in the original finite Cauchy span supplies genuine physical
subsequential vector limits. No new inner product is defined. Fixed finite
order is essential: this does not assert coherence as N tends to infinity. -/
namespace CarryCorrectedGreenPorts
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open CarrySelfAdjointOperator.ChiralReturn
open CarryMaterialMixedSchurComparison
open Filter Bornology
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Only a COMMON scalar changes with k in the actual incident features.
Every regularized incident span lies in the same original finite span. -/
theorem incident_mem_fixedSpan (k N : ℕ)
    (x : CanonicalCompletedNativeChiralCauchyCarrier) (hx : x ∈ RadialIncidentSpan k N) :
    x ∈ RadialIncidentSpan 0 N := by
  obtain ⟨c,rfl⟩ := hx
  refine ⟨fun i => c i * (Real.sqrt ((k : ℝ)+1) : ℂ), ?_⟩
  simp only [radialIncidentSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    completedNativeRadialChiralCauchyState, Nat.cast_zero, zero_add, Real.sqrt_one,
    Complex.ofReal_one, one_smul, smul_smul]

theorem energyJet_mem_fixedSpan (k N : ℕ) (a : Fin N) :
    radialReturnEnergyJet k N a ∈ RadialIncidentSpan 0 N := by
  apply incident_mem_fixedSpan k N
  apply Submodule.smul_mem
  dsimp only [radialReturnEnergyPort, ContinuousLinearMap.comp_apply]
  exact Subtype.property _

theorem residualEnergyJet_mem_fixedSpan (k N : ℕ) (a : Fin (N+1)) :
    residualEnergyJet k N a ∈ RadialIncidentSpan 0 (N+1) :=
  Submodule.sub_mem _ (energyJet_mem_fixedSpan k (N+1) a)
    (Submodule.smul_mem _ _ (energyJet_mem_fixedSpan k (N+1) 0))

/-- A subtype of the existing physical carrier, with exactly its old norm. -/
def fixedPhysicalJet (k N : ℕ) (a : Fin (N+1)) : RadialIncidentSpan 0 (N+1) :=
  ⟨residualEnergyJet k N a, residualEnergyJet_mem_fixedSpan k N a⟩

local instance fixedSpan_finite (N : ℕ) :
    FiniteDimensional ℂ (RadialIncidentSpan 0 N) :=
  (radialIncidentSynthesis 0 N).finiteDimensional_range

/-- A source-level return estimate controls the ENTIRE finite family.
The proof uses bounded physical norms and finite-dimensional compactness,
never a factorization of a target moment matrix. -/
theorem physicalJets_subsequence_of_contractive (N : ℕ)
    (hc : ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k (N+1)‖ ≤ 1) :
    ∃ v : Fin (N+1) → CanonicalCompletedNativeChiralCauchyCarrier,
      ∃ rho : ℕ → ℕ, StrictMono rho ∧
        (∀ a, Tendsto (fun k => residualEnergyJet (rho k) N a) atTop (𝓝 (v a))) ∧
        (∀ a, v a ∈ RadialIncidentSpan 0 (N+1)) := by
  let X (k : ℕ) : Fin (N+1) → RadialIncidentSpan 0 (N+1) := fixedPhysicalJet k N
  have hb (a : Fin (N+1)) : IsBounded (Set.range (fun k => X k a)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp
      (residualEnergyJet_pairing_tendsto_of_contractive N hc a a)
    have hn : Tendsto (fun k => ‖X k a‖^2) atTop
        (𝓝 (carryMaterialResidualJet a.val a.val)) := by
      simpa [X, fixedPhysicalJet, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow,
        carryMaterialResidualJet, Function.comp_def] using h
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
    have hnorm : Tendsto (fun k => ‖X k a‖) atTop
        (𝓝 (Real.sqrt (carryMaterialResidualJet a.val a.val))) := by
      simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hs
    have hb' := Metric.isBounded_range_of_tendsto (fun k => ‖X k a‖) hnorm
    obtain ⟨B,hB⟩ := hb'.exists_norm_le
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨B, ?_⟩
    rintro z ⟨k,rfl⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hB _ ⟨k,rfl⟩
  have hbX : IsBounded (Set.range X) := by
    apply (IsBounded.pi hb).subset
    rintro z ⟨k,rfl⟩ a _
    exact ⟨k,rfl⟩
  obtain ⟨v,_,rho,hrho,hv⟩ := tendsto_subseq_of_bounded hbX (fun k => Set.mem_range_self k)
  refine ⟨fun a => (v a).val, rho, hrho, ?_, fun a => (v a).property⟩
  intro a
  have ha := (tendsto_pi_nhds.mp hv) a
  exact (continuous_subtype_val.tendsto (v a)).comp ha

/-- Exact fixed-vector POSITIVE realization, at finite order, from limits
of the physical ports. The ONLY sign premise is actual return contractivity. -/
theorem correctedGreen_realization_of_contractive (N : ℕ)
    (hc : ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k (N+1)‖ ≤ 1)
    (eta : ℝ) (heta : eta ≠ 0) :
    ∃ v : Fin (N+1) → CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ a, v a ∈ RadialIncidentSpan 0 (N+1)) ∧
      (∀ a b, inner ℂ (v a) (v b) = carryValveConfluentJet eta a.val b.val) := by
  obtain ⟨v,rho,hrho,hv,hmem⟩ := physicalJets_subsequence_of_contractive N hc
  refine ⟨v,hmem,?_⟩
  intro a b
  rw [material_valve_confluent_jet eta heta]
  exact tendsto_nhds_unique ((hv a).inner (hv b))
    ((residualEnergyJet_pairing_tendsto_of_contractive N hc a b).comp hrho.tendsto_atTop)

/-- Seven sources: an unconditional exact positive realization of the
corrected Green jets 0..6 in the ORIGINAL physical L2. No new metric, adjusted
normalization, or factorization of the target Gram enters the construction. -/
theorem correctedGreen_seven_physical_realization (eta : ℝ) (heta : eta ≠ 0) :
    ∃ v : Fin 7 → CanonicalCompletedNativeChiralCauchyCarrier,
      (∀ a, v a ∈ RadialIncidentSpan 0 7) ∧
      (∀ a b, inner ℂ (v a) (v b) = carryValveConfluentJet eta a.val b.val) :=
  correctedGreen_realization_of_contractive 6
    radialReturnTransfer_seven_eventually_norm_le_one eta heta

end
end CarryCorrectedGreenPorts
