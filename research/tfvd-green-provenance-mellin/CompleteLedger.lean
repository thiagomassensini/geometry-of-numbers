import BlockProvenance

namespace CarryGreenProvenance
open CarryFourLeg CarryCameraTail CarryMaterialTheta CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarryC3Crosswalk NativeCarrySpectralWeyl.Boundary
noncomputable section
set_option autoImplicit false

/-- Every field has an independent source expression. In particular,
greenProvenance is NOT the Wronskian minus the other three fields. -/
def heatLedger (M : ℕ) (z w : ℂ) : CanonicalNativePolarizedTfvdGreenLedger where
  greenProvenance := heatGreenProvenance M z w
  crossProvenance :=
    let a := heatMixedLegs M z w
    twoLegBoundaryCrossProvenance a.left a.right a.jetLeft a.jetRight
  readoutResidual := heatReadoutCorrection M z w
  completion := mellinCompletionDefect M z w

/-- Equality of the FOUR-FIELD ledger, following the earlier local record
equalities. Both material parameters remain independent. -/
theorem full_ledger_mellin (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) (hw : 0 < w.re) :
    heatLedger M z w = canonicalNativePolarizedTfvdGreenLedger M z w := by
  unfold heatLedger
  rw [heat_green_eq_original_ledger M hz hz1 hw,
    heat_crosses_eq_original_ledger M hz hw, heat_readout_eq_original_ledger M hz hw,
    mellin_completion_eq_original_ledger M hz hw]

/-- The complete signed identity, including the ACTUAL Green port as an
integral image. This is not an isometry or a positive Gram identity. -/
theorem native_wronskian_full_mellin (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) (hw : 0 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
      greenForm (𝕜 := ℂ) (materialGreenPort (M*3) w)
        (materialGreenPort (M*3) (reflectedParameter z)) +
      (heatLedger M z w).greenProvenance + (heatLedger M z w).crossProvenance +
      (heatLedger M z w).readoutResidual + (heatLedger M z w).completion := by
  rw [full_ledger_mellin M hz hz1 hw,
    green_form_mellin (M*3) hw (reflected_re_pos hz1)]
  have h := canonicalNativePolarizedTfvdGreenLedger_identity M
    (show -1 < z.re by linarith) (show -1 < w.re by linarith)
  rw [Nat.mul_comm 3 M] at h
  exact h

end
end CarryGreenProvenance
