import PrimeCarryGate

namespace CarryTiltSlice
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false

/-- The height and transverse derivatives are distinct directions. -/
theorem height_jets_zero_transverse_sensitivity_pos (M : ℕ) (hM : 0 < M) :
    (∀ n : ℕ, ∀ t : ℝ,
      iteratedDeriv n (fun u : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (criticalParameter u)) t = 0) ∧
    0 < deriv (finiteCanonicalRealCriticalWeightedTiltTrace M) 0 :=
  ⟨fun n t => finite_tilt_vertical_jets_zero M n t, transverse_sensitivity_positive M hM⟩

/-- The positive tilt sensitivity has an explicit carrier/cross companion. -/
theorem transverse_global_ledger :
    (-canonicalCompletedC3EnrichedTfvdLogJetTailReadout (1/2:ℂ)).re =
        canonicalRealCriticalWeightedTiltTotalSensitivity +
          canonicalRealCriticalCarrierRemainderTotalSensitivity ∧
      0 < canonicalRealCriticalWeightedTiltTotalSensitivity :=
  ⟨completedNativeLogJetRealFirstVariation_eq_tilt_add_remainder,
    canonicalRealCriticalWeightedTiltTotalSensitivity_pos⟩

#print axioms height_jets_zero_transverse_sensitivity_pos
#print axioms transverse_global_ledger
end
end CarryTiltSlice
