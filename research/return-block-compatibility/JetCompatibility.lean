import PortTransitions

namespace CarryReturnCompatibility
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open CarryCorrectedGreenPorts
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The old finite-difference coefficients synthesize the SAME incident jet
when its source block is enlarged. No camera/jet indices are identified. -/
theorem differenceInput_inclusion (k : ℕ) {N M : ℕ} (h : N ≤ M) (a : Fin N) :
    incidentInclusion k h
      (radialIncidentVector k N (radialDifferenceSourceCoefficients k N a.val)) =
      radialIncidentVector k M
        (radialDifferenceSourceCoefficients k M (Fin.castLE h a).val) := by
  apply Subtype.ext
  change radialIncidentSynthesis k N (radialDifferenceSourceCoefficients k N a.val) =
    radialIncidentSynthesis k M (radialDifferenceSourceCoefficients k M a.val)
  exact (congrArg Prod.fst (radialDifferenceSource_pair k N a.val a.isLt)).trans
    (congrArg Prod.fst (radialDifferenceSource_pair k M a.val
      (lt_of_lt_of_le a.isLt h))).symm

def energyJetSource (k N : ℕ) (a : Fin N) : RadialIncidentSpan k N :=
  (Real.sqrt 2 : ℂ)⁻¹ •
    radialIncidentVector k N (radialDifferenceSourceCoefficients k N a.val)

theorem energyJetSource_port (k N : ℕ) (a : Fin N) :
    radialReturnEnergyPort k N (energyJetSource k N a) = radialReturnEnergyJet k N a := by
  rw [energyJetSource, map_smul]
  rfl

theorem energyJetSource_inclusion (k : ℕ) {N M : ℕ} (h : N ≤ M) (a : Fin N) :
    incidentInclusion k h (energyJetSource k N a) = energyJetSource k M (Fin.castLE h a) := by
  rw [energyJetSource, map_smul, differenceInput_inclusion]
  rfl

/-- The same scalar source-axis extraction is performed before either port. -/
def residualJetSource (k N : ℕ) (a : Fin (N+1)) : RadialIncidentSpan k (N+1) :=
  energyJetSource k (N+1) a-sourceCenterWeight a.val • energyJetSource k (N+1) 0

theorem residualJetSource_port (k N : ℕ) (a : Fin (N+1)) :
    radialReturnEnergyPort k (N+1) (residualJetSource k N a) = residualEnergyJet k N a := by
  rw [residualJetSource, map_sub, map_smul, energyJetSource_port, energyJetSource_port]
  rfl

theorem residualJetSource_inclusion (k : ℕ) {N M : ℕ} (h : N ≤ M) (a : Fin (N+1)) :
    incidentInclusion k (Nat.add_le_add_right h 1) (residualJetSource k N a) =
      residualJetSource k M (Fin.castLE (Nat.add_le_add_right h 1) a) := by
  rw [residualJetSource, map_sub, map_smul, energyJetSource_inclusion, energyJetSource_inclusion]
  rfl

def residualJetImage (k N : ℕ) (a : Fin (N+1)) : PhysicalEnergyRange k (N+1) :=
  ⟨radialReturnEnergyPort k (N+1) (residualJetSource k N a),⟨residualJetSource k N a,rfl⟩⟩

/-- Exact compatibility of the source-derived residual jets at EVERY size,
whenever the larger physical return is contractive. It is an actual isometry
between the energy image subspaces, not literal equality of square roots. -/
theorem residualJetImage_transition (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (hM : ‖radialReturnTransfer k (M+1)‖ ≤ 1) (a : Fin (N+1)) :
    energyTransition k (Nat.add_le_add_right h 1) hM (residualJetImage k N a) =
      residualJetImage k M (Fin.castLE (Nat.add_le_add_right h 1) a) := by
  apply Subtype.ext
  rw [residualJetImage, energyTransition_source, residualJetSource_inclusion k h a]
  rfl

/-- Independent left/right orders and every crossing are compatible under
the source-induced transition, before any diagonal energy readout. -/
theorem residualJets_prefix_pairing (k : ℕ) {N M : ℕ} (h : N ≤ M)
    (hM : ‖radialReturnTransfer k (M+1)‖ ≤ 1) (a b : Fin (N+1)) :
    inner ℂ (residualEnergyJet k M (Fin.castLE (Nat.add_le_add_right h 1) a))
      (residualEnergyJet k M (Fin.castLE (Nat.add_le_add_right h 1) b)) =
      inner ℂ (residualEnergyJet k N a) (residualEnergyJet k N b) := by
  rw [← residualJetSource_port, ← residualJetSource_port,
    ← residualJetSource_inclusion k h a, ← residualJetSource_inclusion k h b,
    energyPort_prefix_pairing k (Nat.add_le_add_right h 1) hM,
    residualJetSource_port, residualJetSource_port]

end
end CarryReturnCompatibility
