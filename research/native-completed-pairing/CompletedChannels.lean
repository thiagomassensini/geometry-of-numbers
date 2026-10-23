import CompletedSource
import CarrySelfAdjointOperator.CompletedC3FNegFPrimeMixedKernel

/-! The completed SIX-CHANNEL ledger already exists in the operator.
This module transports its fields, rather than inventing a replacement.
The raw four-field ledger remains inside the construction; rotating the
height companion changes its readout and tail corrections explicitly. -/
namespace CarryCompletedPairing
open CarryCameraTail CarryMaterialTheta CarryFourLeg CarryGreenProvenance
open CarrySelfAdjointOperator CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open NativeCarrySpectralWeyl.Boundary
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

def integralHeightReadout (M : ℕ) (z w : ℂ) : ℂ :=
  let p := materialHeadTrace M (operatorHeightParameter z)
  let q := materialHeadTrace M (operatorHeightParameter w)
  mixedBoundaryResidualCorrection p.1 (Complex.I*p.2) q.1 (Complex.I*q.2)
    (heatMixedLegs M (operatorHeightParameter z) (operatorHeightParameter w))

theorem height_readout_mellin (M : ℕ) {z w : ℂ}
    (hz : 0 < (operatorHeightParameter z).re) (hw : 0 < (operatorHeightParameter w).re) :
    integralHeightReadout M z w =
      canonicalMixedBoundaryHeightReadoutResidualCorrection M tfvdHaarScale (fun _ => 1)
        (operatorHeightParameter z) (operatorHeightParameter w) := by
  unfold integralHeightReadout
  rw [material_head_trace_eq M hz, material_head_trace_eq M hw,
    original_four_legs_mellin M hz hw]
  rfl

def integralHeightTail (M : ℕ) (z w : ℂ) : ℂ :=
  let p := gammaUndress (operatorHeightParameter z)
    (heatTrace (cameraHeatHead M) (operatorHeightParameter z))
  let q := gammaUndress (operatorHeightParameter w)
    (heatTrace (cameraHeatHead M) (operatorHeightParameter w))
  let a := gammaUndress (operatorHeightParameter z) (heatTailTrace M (operatorHeightParameter z))
  let b := gammaUndress (operatorHeightParameter w) (heatTailTrace M (operatorHeightParameter w))
  mixedBoundaryCompletionCorrection p.1 (Complex.I*p.2) q.1 (Complex.I*q.2)
    a.1 (Complex.I*a.2) b.1 (Complex.I*b.2)

theorem height_tail_mellin (M : ℕ) {z w : ℂ}
    (hz : 0 < (operatorHeightParameter z).re) (hw : 0 < (operatorHeightParameter w).re) :
    integralHeightTail M z w = canonicalC3MixedHeightTailCompletionDefect M z w := by
  unfold integralHeightTail
  rw [native_head_from_heat M hz, native_head_from_heat M hw,
    native_tail_from_heat M hz, native_tail_from_heat M hw]
  rfl

/-- The original archimedean/chart product channel, whose value factors
are now the tail-completed Mellin source. Both Wronskians are retained. -/
def integralArchimedeanChannel (M : ℕ) (z w : ℂ) : ℂ :=
  let p := integralMaterialTrace M (operatorHeightParameter z)
  let q := integralMaterialTrace M (operatorHeightParameter w)
  (p.1 / canonicalC3ChartFactorHeight z) * conj (q.1 / canonicalC3ChartFactorHeight w) *
    (mixedHermitianWeight canonicalC3ChartFactorHeight z w *
      completedGreenWronskian nativeXiCompletionFactor nativeXiCompletionBoundaryCompanion z w -
     mixedHermitianWeight nativeXiCompletionFactor z w *
      completedGreenWronskian canonicalC3ChartFactorHeight
        canonicalC3ChartFactorHeightCompanion z w)

theorem archimedean_channel_mellin (M : ℕ) {z w : ℂ}
    (hz : 0 < (operatorHeightParameter z).re) (hw : 0 < (operatorHeightParameter w).re) :
    integralArchimedeanChannel M z w = canonicalCompletedC3ArchimedeanChartMixedChannel z w := by
  unfold integralArchimedeanChannel
  rw [integral_material_trace_eq M hz, integral_material_trace_eq M hw,
    canonicalC3BracketTfvdCompletionState_valueReadout_eq_completed M
      (show operatorHeightParameter z ∈ bracketHalfPlane by
        simpa [bracketHalfPlane] using (show -1 < (operatorHeightParameter z).re by linarith)),
    canonicalC3BracketTfvdCompletionState_valueReadout_eq_completed M
      (show operatorHeightParameter w ∈ bracketHalfPlane by
        simpa [bracketHalfPlane] using (show -1 < (operatorHeightParameter w).re by linarith))]
  rfl

def integralCompletedChannels (M : ℕ) (z w : ℂ) : CanonicalCompletedC3FNegFPrimeMixedChannels :=
  let sz := operatorHeightParameter z
  let sw := operatorHeightParameter w
  let a := mixedHermitianWeight nativeXiCompletionFactor z w
  {
    radialGreen := a * greenForm (𝕜 := ℂ) (materialGreenPort (M*3) sw)
      (materialGreenPort (M*3) (reflectedParameter sz))
    greenProvenance := a * (heatLedger M sz sw).greenProvenance
    offDiagonal := a * (heatLedger M sz sw).crossProvenance
    readoutResidual := a * integralHeightReadout M z w
    tailCompletion := a * integralHeightTail M z w
    archimedeanChart := integralArchimedeanChannel M z w
  }

/-- Entire SIX-FIELD record equality, before finalReadout. Local blocks of
greenProvenance retain the nine-field identification from PR #75. -/
theorem completed_channels_mellin (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    integralCompletedChannels M z w = canonicalCompletedC3FiniteFNegFPrimeMixedChannels M z w := by
  unfold integralCompletedChannels
  dsimp only
  rw [green_form_mellin _ hw.1 (reflected_re_pos hz.2),
    full_ledger_mellin M hz.1 hz.2 hw.1,
    height_readout_mellin M hz.1 hw.1, height_tail_mellin M hz.1 hw.1,
    archimedean_channel_mellin M hz.1 hw.1]
  rw [Nat.mul_comm M 3]
  rfl

theorem completed_channels_pairing (M : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    (integralCompletedChannels M z w).finalReadout /
      mixedHermitianWeight canonicalC3ChartFactorHeight z w =
        completedIntegralPairing M M z w := by
  rw [completed_channels_mellin M hz hw,
    finalScalarReadout_div_chartWeight_eq_completedFNegFPrimeWronskian M hz hw,
    completed_pairing_eq_original M M hz hw]
  rfl

end
end CarryCompletedPairing
