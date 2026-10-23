import RadialCompensation

namespace CarryGreenProvenance
open CarryFourLeg CarryCameraTail CarryMaterialTheta CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarryC3Crosswalk NativeCarrySpectralWeyl.Boundary
open Filter
noncomputable section
set_option autoImplicit false

/-- This readout is applied only after every local channel has been
calibrated and the four-field ledger has been identified. -/
def heatLedgerTotal (M : ℕ) (z w : ℂ) : ℂ :=
  (heatLedger M z w).greenProvenance + (heatLedger M z w).crossProvenance +
    (heatLedger M z w).readoutResidual + (heatLedger M z w).completion

theorem heat_ledger_total_eq_native_defect (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) (hw : 0 < w.re) :
    heatLedgerTotal M z w = canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w := by
  rw [canonicalNativePolarizedTfvdGreenMomentKernelDefect_eq_ledger_total,
    heatLedgerTotal, full_ledger_mellin M hz hz1 hw]

/-- The entire transported ledger has the ORIGINAL defect limit. This
does not replace that limit by zero, or exchange an infinite Mellin sum
with the unrenormalized raw material input. -/
theorem heat_ledger_total_tendsto {z w : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) (hw : 0 < w.re) :
    Tendsto (fun M : ℕ => heatLedgerTotal M z w) atTop
      (nhds (canonicalCompletedC3RawMixedWronskian z w -
        canonicalCompletedC3MixedRadialGreenKernel z w hw (reflected_re_pos hz1))) := by
  have h := canonicalNativePolarizedTfvdGreenMomentKernelDefect_tendsto hz hz1 hw
  have heq : (fun M : ℕ => heatLedgerTotal M z w) =
      (fun M : ℕ => canonicalNativePolarizedTfvdGreenMomentKernelDefect M z w) := by
    funext M
    exact heat_ledger_total_eq_native_defect M hz hz1 hw
  rw [heq]
  exact h

theorem heat_completion_tendsto_zero {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Tendsto (fun M : ℕ => (heatLedger M z w).completion) atTop (nhds 0) := by
  have heq : (fun M : ℕ => (heatLedger M z w).completion) =
      (fun M : ℕ => canonicalC3MixedTailCompletionDefect M z w) := by
    funext M
    exact mellin_completion_eq_original_ledger M hz hw
  rw [heq]
  exact canonicalC3MixedTailCompletionDefect_tendsto_zero hz hw

/-- On the critical product the TOTAL correction is independent of the
cutoff, although its four separate fields need not be independent. -/
theorem critical_ledger_total_eq (M : ℕ) {z w : ℂ}
    (hz : z.re = 1/2) (hw : w.re = 1/2) :
    heatLedgerTotal M z w = canonicalCompletedC3RawMixedWronskian z w :=
  (critical_wronskian_in_ledger M hz hw).symm

theorem critical_ledger_total_cutoff_independent (M N : ℕ) {z w : ℂ}
    (hz : z.re = 1/2) (hw : w.re = 1/2) :
    heatLedgerTotal M z w = heatLedgerTotal N z w := by
  rw [critical_ledger_total_eq M hz hw, critical_ledger_total_eq N hz hw]

end
end CarryGreenProvenance
