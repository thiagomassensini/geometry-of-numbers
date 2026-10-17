import PositivePorts

/-! Whole finite superpositions are synthesized in the OLD physical Cauchy
carrier before scalar energy is taken. The limit is the corrected Green
jet pairing, with all ordered complex coefficient crosses retained. -/
namespace CarryCorrectedGreenPorts
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open CarrySelfAdjointOperator.ChiralReturn
open CarryMaterialMixedSchurComparison
open Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def residualEnergySynthesis (k N : ℕ) (x : Fin (N+1) → ℂ) :
    CanonicalCompletedNativeChiralCauchyCarrier :=
  ∑ a, x a • residualEnergyJet k N a

/-- An observation of the existing residual, not a metric definition. -/
def residualJetBilinear (N : ℕ) (x y : Fin (N+1) → ℂ) : ℂ :=
  ∑ a, ∑ b, conj (x a)*y b*
    carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) a.val b.val

theorem residualEnergySynthesis_pairing (k N : ℕ) (x y : Fin (N+1) → ℂ) :
    inner ℂ (residualEnergySynthesis k N x) (residualEnergySynthesis k N y) =
      ∑ a, ∑ b, conj (x a)*y b*inner ℂ (residualEnergyJet k N a) (residualEnergyJet k N b) := by
  simp only [residualEnergySynthesis, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The finite return estimate is geometric, preceding every moment or
energy extraction. The inputs x,y are arbitrary and independent. -/
theorem residualEnergySynthesis_pairing_tendsto_of_contractive (N : ℕ)
    (hc : ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k (N+1)‖ ≤ 1)
    (x y : Fin (N+1) → ℂ) :
    Tendsto (fun k => inner ℂ (residualEnergySynthesis k N x) (residualEnergySynthesis k N y))
      atTop (𝓝 (residualJetBilinear N x y)) := by
  simp only [residualEnergySynthesis_pairing, residualJetBilinear]
  apply tendsto_finsetSum
  intro a _
  apply tendsto_finsetSum
  intro b _
  exact (residualEnergyJet_pairing_tendsto_of_contractive N hc a b).const_mul _

theorem residualEnergySynthesis_seven_pairing_tendsto (x y : Fin 7 → ℂ) :
    Tendsto (fun k => inner ℂ (residualEnergySynthesis k 6 x) (residualEnergySynthesis k 6 y))
      atTop (𝓝 (residualJetBilinear 6 x y)) :=
  residualEnergySynthesis_pairing_tendsto_of_contractive 6
    radialReturnTransfer_seven_eventually_norm_le_one x y

/-- Exact destination is the physical valve's confluent Green ledger, with
both original input orders and complex coefficients still present. -/
theorem correctedGreen_seven_synthesis_pairing_tendsto
    (eta : ℝ) (heta : eta ≠ 0) (x y : Fin 7 → ℂ) :
    Tendsto (fun k => inner ℂ (residualEnergySynthesis k 6 x) (residualEnergySynthesis k 6 y))
      atTop (𝓝 (∑ a : Fin 7, ∑ b : Fin 7,
        conj (x a)*y b*carryValveConfluentJet eta a.val b.val)) := by
  simp_rw [material_valve_confluent_jet eta heta]
  exact residualEnergySynthesis_seven_pairing_tendsto x y

theorem residualEnergySynthesis_seven_norm_sq_tendsto (x : Fin 7 → ℂ) :
    Tendsto (fun k => ‖residualEnergySynthesis k 6 x‖^2) atTop
      (𝓝 (residualJetBilinear 6 x x).re) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (residualEnergySynthesis_seven_pairing_tendsto x x)
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Function.comp_def] using h

/-- A source-derived positive approximation, for EVERY complex combination
in the fixed block. No selected diagonal tests replace polarization. -/
theorem correctedGreen_seven_energy_nonnegative (x : Fin 7 → ℂ) :
    0 ≤ (residualJetBilinear 6 x x).re := by
  apply ge_of_tendsto (residualEnergySynthesis_seven_norm_sq_tendsto x)
  exact Filter.Eventually.of_forall (fun k => sq_nonneg _)

/-- What a genuine fixed-vector realization would need in addition to Gram
convergence: physical vector limits. They are NOT supplied by this theorem. -/
theorem correctedGreen_seven_pairing_of_physical_limits
    (v : Fin 7 → CanonicalCompletedNativeChiralCauchyCarrier)
    (hv : ∀ a, Tendsto (fun k => residualEnergyJet k 6 a) atTop (𝓝 (v a)))
    (eta : ℝ) (heta : eta ≠ 0) (a b : Fin 7) :
    inner ℂ (v a) (v b) = carryValveConfluentJet eta a.val b.val := by
  exact tendsto_nhds_unique ((hv a).inner (hv b))
    (correctedGreen_seven_positive_pairing_tendsto eta heta a b)

/-- The exact missing cross-regularization quantity: same-cutoff Gram limits
do not by themselves evaluate this mixed k,l term or make vectors Cauchy. -/
theorem residualEnergyJet_mixed_cutoff_distance (k l N : ℕ) (a : Fin (N+1)) :
    ‖residualEnergyJet k N a-residualEnergyJet l N a‖^2 =
      ‖residualEnergyJet k N a‖^2+‖residualEnergyJet l N a‖^2-
        2*(inner ℂ (residualEnergyJet k N a) (residualEnergyJet l N a)).re := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  change ‖residualEnergyJet k N a‖^2-
    2*(inner ℂ (residualEnergyJet k N a) (residualEnergyJet l N a)).re+
      ‖residualEnergyJet l N a‖^2 = _
  ring

end
end CarryCorrectedGreenPorts
