import TailControl
import CarrySelfAdjointOperator.CompletedNativePolarizedTfvdGreenMomentKernel

namespace CarryCameraTail
open CarryMaterialTheta CarrySelfAdjointOperator CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- Inverse of the proven Gamma trace transport, on Re(s)>0. This only
undoes a known nonzero analytic factor; it is not a metric or a Gram fit. -/
def gammaUndress (s : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (p.1 / Complex.Gammaℝ s,
   p.2 / Complex.Gammaℝ s + deriv Complex.Gammaℝ s*p.1/(Complex.Gammaℝ s)^2)

theorem gammaUndress_gammaDress {s : ℂ} (hs : 0 < s.re) (p : ℂ × ℂ) :
    gammaUndress s (gammaDress s p) = p := by
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos hs
  apply Prod.ext
  · simp [gammaUndress, gammaDress, hg]
  · simp only [gammaUndress, gammaDress]
    field_simp
    ring

theorem gammaDress_gammaUndress {s : ℂ} (hs : 0 < s.re) (p : ℂ × ℂ) :
    gammaDress s (gammaUndress s p) = p := by
  have hg := Complex.Gammaℝ_ne_zero_of_re_pos hs
  apply Prod.ext
  · dsimp [gammaUndress, gammaDress]
    field_simp
  · simp only [gammaUndress, gammaDress]
    field_simp
    ring

theorem gammaUndress_add (s : ℂ) (p q : ℂ × ℂ) :
    gammaUndress s (p+q) = gammaUndress s p + gammaUndress s q := by
  apply Prod.ext
  · simp [gammaUndress, add_div]
  · simp [gammaUndress, add_div]
    ring

theorem native_head_from_heat (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    gammaUndress s (heatTrace (cameraHeatHead M) s) = nativeHeadTrace M s := by
  rw [camera_head_trace_calibration M hs, gammaUndress_gammaDress hs]

theorem native_tail_from_heat (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    gammaUndress s (heatTailTrace M s) = nativeTailTrace M s := by
  rw [original_stored_tail_trace M hs, gammaUndress_gammaDress hs]
  rfl

/-- The exact existing six-term tail correction, read from the actual
Mellin integrals. The conjugated independent input is retained. -/
def mellinCompletionDefect (M : ℕ) (z w : ℂ) : ℂ :=
  let h := gammaUndress z (heatTrace (cameraHeatHead M) z)
  let k := gammaUndress w (heatTrace (cameraHeatHead M) w)
  let a := gammaUndress z (heatTailTrace M z)
  let b := gammaUndress w (heatTailTrace M w)
  mixedBoundaryCompletionCorrection h.1 h.2 k.1 k.2 a.1 a.2 b.1 b.2

theorem mellin_completion_eq_original_ledger (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) :
    mellinCompletionDefect M z w =
      (canonicalNativePolarizedTfvdGreenLedger M z w).completion := by
  unfold mellinCompletionDefect
  rw [native_head_from_heat M hz, native_head_from_heat M hw,
    native_tail_from_heat M hz, native_tail_from_heat M hw]
  rfl

/-- The remaining ledger fields are retained verbatim. Transporting the
completion channel does not make the structural defect vanish. -/
theorem native_ledger_with_mellin_completion (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hw : 0 < w.re) :
    canonicalCompletedC3RawMixedWronskian z w =
      greenForm (𝕜 := ℂ)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair (3*M) w)
        (NativeCarryC3Crosswalk.finiteC3GenuineBracketGreenBoundaryPair (3*M) (reflectedParameter z)) +
      (canonicalNativePolarizedTfvdGreenLedger M z w).greenProvenance +
      (canonicalNativePolarizedTfvdGreenLedger M z w).crossProvenance +
      (canonicalNativePolarizedTfvdGreenLedger M z w).readoutResidual +
      mellinCompletionDefect M z w := by
  rw [mellin_completion_eq_original_ledger M hz hw]
  exact canonicalNativePolarizedTfvdGreenLedger_identity M (by linarith) (by linarith)

/-- The ORIGINAL camera quotient, height derivative factor I, polynomial
dressing and completion companion. Inputs are already synthesized traces. -/
def nativeCompletionTrace (z : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  let s := operatorHeightParameter z
  let C := cpChartFactor 3 s
  let C' := deriv (cpChartFactor 3) s
  let A := nativeXiCompletionFactor z
  let A' := nativeXiCompletionBoundaryCompanion z
  (A*(p.1/C), A'*(p.1/C) + A*(Complex.I*((p.2*C+p.1*C')/C^2)))

/-- The transported head and tails recover the original completed trace,
with all camera and product-rule terms, at the actual height parameter. -/
theorem native_completed_trace_from_mellin (M : ℕ) (z : ℂ)
    (hz : 0 < (operatorHeightParameter z).re) :
    nativeCompletionTrace z
      (gammaUndress (operatorHeightParameter z)
        (heatTrace (cameraHeatHead M) (operatorHeightParameter z) +
         heatTailTrace M (operatorHeightParameter z))) =
      canonicalC3BracketTfvdCompletedTracePair M z := by
  rw [completed_heat_trace_calibration M hz, gammaUndress_gammaDress hz]
  rfl

theorem nativeCompletionTrace_add (z : ℂ) (p q : ℂ × ℂ) :
    nativeCompletionTrace z (p+q) = nativeCompletionTrace z p + nativeCompletionTrace z q := by
  apply Prod.ext <;> simp [nativeCompletionTrace, add_div] <;> ring

def completedHeatHead (M : ℕ) (z : ℂ) : ℂ × ℂ :=
  nativeCompletionTrace z (gammaUndress (operatorHeightParameter z)
    (heatTrace (cameraHeatHead M) (operatorHeightParameter z)))

def completedHeatTail (M : ℕ) (z : ℂ) : ℂ × ℂ :=
  nativeCompletionTrace z (gammaUndress (operatorHeightParameter z)
    (heatTailTrace M (operatorHeightParameter z)))

theorem original_completed_trace_head_tail (M : ℕ) (z : ℂ)
    (hz : 0 < (operatorHeightParameter z).re) :
    canonicalC3BracketTfvdCompletedTracePair M z =
      completedHeatHead M z + completedHeatTail M z := by
  rw [← native_completed_trace_from_mellin M z hz, gammaUndress_add, nativeCompletionTrace_add]
  rfl

/-- Crossings after the original camera quotient and Xi completion, not
only in the raw or Gamma-dressed trace. Independent probes are complex. -/
theorem completed_native_green_four_crosses (M N : ℕ) (z w a b c d : ℂ) :
    greenForm (𝕜 := ℂ)
      (a • completedHeatHead M z + b • completedHeatTail M z)
      (c • completedHeatHead N w + d • completedHeatTail N w) =
      conj a*c*greenForm (𝕜 := ℂ) (completedHeatHead M z) (completedHeatHead N w) +
      conj a*d*greenForm (𝕜 := ℂ) (completedHeatHead M z) (completedHeatTail N w) +
      conj b*c*greenForm (𝕜 := ℂ) (completedHeatTail M z) (completedHeatHead N w) +
      conj b*d*greenForm (𝕜 := ℂ) (completedHeatTail M z) (completedHeatTail N w) := by
  simp only [greenForm, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  ring

end
end CarryCameraTail
