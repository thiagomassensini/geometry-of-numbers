import MixedLegs

namespace CarryFourLeg
open CarryCameraTail CarryMaterialTheta CarrySelfAdjointOperator CPFormal.Analytic.Cp
open NativeCarryC3Crosswalk NativeCarrySpectralWeyl.Boundary
noncomputable section
set_option autoImplicit false

def materialHeadTrace (M : ℕ) (s : ℂ) : ℂ × ℂ :=
  gammaUndress s (heatTrace (cameraHeatHead M) s)

theorem material_head_trace_eq (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    materialHeadTrace M s =
      ((canonicalBoundaryResidualData M tfvdHaarScale (fun _ => 1) s).valueReadout,
       (canonicalBoundaryResidualData M tfvdHaarScale (fun _ => 1) s).logJetReadout) := by
  rw [materialHeadTrace, native_head_from_heat M hs]
  have hv := (canonicalC3BracketTfvdCompletionState_transport_components M s).1
  have hl := (canonicalC3BracketTfvdCompletionState_transport_components M s).2.1
  change (canonicalBoundaryResidualData M tfvdHaarScale (fun _ => 1) s).valueReadout = _ at hv
  change (canonicalBoundaryResidualData M tfvdHaarScale (fun _ => 1) s).logJetReadout = _ at hl
  rw [hv, hl]
  rfl

/-- The four linear residuals remain distinct until the bilinear readout.
The head and every local edge are computed from literal Mellin integrals. -/
def heatReadoutResiduals (M : ℕ) (z w : ℂ) : ℂ × (ℂ × (ℂ × ℂ)) :=
  let p := materialHeadTrace M z
  let q := materialHeadTrace M w
  let legs := heatMixedLegs M z w
  (mixedBoundaryLeftResidual q.2 legs,
   (mixedBoundaryRightResidual q.1 legs,
    (mixedBoundaryJetLeftResidual p.2 legs,
     mixedBoundaryJetRightResidual p.1 legs)))

def originalReadoutResiduals (M : ℕ) (z w : ℂ) : ℂ × (ℂ × (ℂ × ℂ)) :=
  let p := canonicalBoundaryResidualData M tfvdHaarScale (fun _ => 1) z
  let q := canonicalBoundaryResidualData M tfvdHaarScale (fun _ => 1) w
  let legs := canonicalMixedBoundaryResidualLegs M tfvdHaarScale (fun _ => 1) z w
  (mixedBoundaryLeftResidual q.logJetReadout legs,
   (mixedBoundaryRightResidual q.valueReadout legs,
    (mixedBoundaryJetLeftResidual p.logJetReadout legs,
     mixedBoundaryJetRightResidual p.valueReadout legs)))

theorem four_readout_residuals_mellin (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) :
    heatReadoutResiduals M z w = originalReadoutResiduals M z w := by
  unfold heatReadoutResiduals
  rw [material_head_trace_eq M hz, material_head_trace_eq M hw,
    original_four_legs_mellin M hz hw]
  rfl

/-- The original six-term bilinear correction, with all cross-residual
terms. It is not defined as a desired Wronskian minus a Green form. -/
def heatReadoutCorrection (M : ℕ) (z w : ℂ) : ℂ :=
  let p := materialHeadTrace M z
  let q := materialHeadTrace M w
  mixedBoundaryResidualCorrection p.1 p.2 q.1 q.2 (heatMixedLegs M z w)

theorem heat_readout_eq_original_ledger (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) :
    heatReadoutCorrection M z w =
      (canonicalNativePolarizedTfvdGreenLedger M z w).readoutResidual := by
  unfold heatReadoutCorrection
  rw [material_head_trace_eq M hz, material_head_trace_eq M hw,
    original_four_legs_mellin M hz hw]
  rfl

/-- Ordered crosses between all block/edge labels, after vector calibration. -/
theorem heat_crosses_eq_original_ledger (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) :
    let a := heatMixedLegs M z w
    twoLegBoundaryCrossProvenance a.left a.right a.jetLeft a.jetRight =
      (canonicalNativePolarizedTfvdGreenLedger M z w).crossProvenance := by
  dsimp only
  rw [original_four_legs_mellin M hz hw]
  rfl

theorem native_ledger_with_mellin_readout (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) :
    let a := heatMixedLegs M z w
    canonicalCompletedC3RawMixedWronskian z w =
      greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair (3*M) w)
        (finiteC3GenuineBracketGreenBoundaryPair (3*M) (reflectedParameter z)) +
      (canonicalNativePolarizedTfvdGreenLedger M z w).greenProvenance +
      twoLegBoundaryCrossProvenance a.left a.right a.jetLeft a.jetRight +
      heatReadoutCorrection M z w + mellinCompletionDefect M z w := by
  dsimp only
  rw [heat_crosses_eq_original_ledger M hz hw, heat_readout_eq_original_ledger M hz hw]
  exact native_ledger_with_mellin_completion M hz hw

end
end CarryFourLeg
