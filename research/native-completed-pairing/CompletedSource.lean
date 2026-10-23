import CompletionAction

namespace CarryCompletedPairing
open CarryCameraTail CarryMaterialTheta CarryFourLeg CarryGreenProvenance
open CarrySelfAdjointOperator CPFormal.Analytic.Cp NativeCarryC3Crosswalk
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- All THREE residues of every original C3 block, each with value and
log jet. This is an indexed coordinate family, not a new Hilbert metric. -/
def completedIntegralCells (M : ℕ) (z : ℂ) : (Fin M × Fin 3) → ℂ × ℂ :=
  fun mr => nativeCompletionTrace z
    (materialEdgeTrace (3*mr.1.val+mr.2.val) (operatorHeightParameter z))

def completedNativeCells (M : ℕ) (z : ℂ) : (Fin M × Fin 3) → ℂ × ℂ :=
  fun mr => nativeCompletionTrace z
    (positiveDirichletGradient (operatorHeightParameter z) (3*mr.1.val+mr.2.val),
     positiveLogDirichletGradient (operatorHeightParameter z) (3*mr.1.val+mr.2.val))

/-- Vector-valued equality before any pairing or sum. No cell label,
quadrature, or jet coordinate is removed. -/
theorem completed_cells_mellin (M : ℕ) (z : ℂ)
    (hz : 0 < (operatorHeightParameter z).re) :
    completedIntegralCells M z = completedNativeCells M z := by
  funext mr
  unfold completedIntegralCells completedNativeCells
  rw [material_edge_trace_eq _ hz]

theorem completed_cells_two_inputs (M N : ℕ) (z w : ℂ)
    (mz : Fin M × Fin 3) (nw : Fin N × Fin 3)
    (hz : 0 < (operatorHeightParameter z).re) (hw : 0 < (operatorHeightParameter w).re) :
    (completedIntegralCells M z mz, completedIntegralCells N w nw) =
      (completedNativeCells M z mz, completedNativeCells N w nw) := by
  rw [completed_cells_mellin M z hz, completed_cells_mellin N w hw]

theorem completed_cell_pairing (M N : ℕ) (z w : ℂ)
    (mz : Fin M × Fin 3) (nw : Fin N × Fin 3)
    (hz : 0 < (operatorHeightParameter z).re) (hw : 0 < (operatorHeightParameter w).re) :
    mixedScalarBoundaryWedge
      (completedIntegralCells M z mz).1 (completedIntegralCells M z mz).2
      (completedIntegralCells N w nw).1 (completedIntegralCells N w nw).2 =
    mixedScalarBoundaryWedge
      (completedNativeCells M z mz).1 (completedNativeCells M z mz).2
      (completedNativeCells N w nw).1 (completedNativeCells N w nw).2 := by
  rw [completed_cells_mellin M z hz, completed_cells_mellin N w hw]

/-- Seed, head and both stored tails are synthesized by the existing
construction. This input remains a value/log-jet pair, not the distinct
radial/horizontal Green port. -/
def integralMaterialTrace (M : ℕ) (s : ℂ) : ℂ × ℂ :=
  gammaUndress s (heatTrace (cameraHeatHead M) s + heatTailTrace M s)

theorem integral_material_trace_eq (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    integralMaterialTrace M s =
      ((canonicalC3BracketTfvdCompletionState M s).valueReadout,
       (canonicalC3BracketTfvdCompletionState M s).logJetReadout) := by
  rw [integralMaterialTrace, completed_heat_trace_calibration M hs,
    gammaUndress_gammaDress hs]

theorem integral_material_trace_eq_raw (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    integralMaterialTrace M s =
      (bracketedDirichletChart 3 s, canonicalCompletedC3EnrichedTfvdLogJetTailReadout s) := by
  rw [integral_material_trace_eq M hs,
    canonicalC3BracketTfvdCompletionState_valueReadout_eq_completed M
      (show s ∈ bracketHalfPlane by simpa [bracketHalfPlane] using (show -1 < s.re by linarith)),
    canonicalC3BracketTfvdCompletionState_logJetReadout_eq_completed M
      (show s ∈ bracketHalfPlane by simpa [bracketHalfPlane] using (show -1 < s.re by linarith))]
  apply Prod.ext
  · change canonicalCompletedC3EnrichedTfvdValueTailReadout s = _
    unfold canonicalCompletedC3EnrichedTfvdValueTailReadout
    exact finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
      1 tfvdHaarScale_ne_zero (fun _ => 1) (by simp) (by linarith)
  · rfl

def completedIntegralTrace (M : ℕ) (z : ℂ) : ℂ × ℂ :=
  nativeCompletionTrace z (integralMaterialTrace M (operatorHeightParameter z))

/-- Equality of the synthesized completed vectors, before the scalar
Wronskian projection. Both tails are still in the source expression. -/
theorem completed_trace_mellin (M : ℕ) (z : ℂ)
    (hz : 0 < (operatorHeightParameter z).re) :
    completedIntegralTrace M z = canonicalC3BracketTfvdCompletedTracePair M z := by
  exact native_completed_trace_from_mellin M z hz

def completedIntegralPairing (M N : ℕ) (z w : ℂ) : ℂ :=
  mixedScalarBoundaryWedge
    (completedIntegralTrace M z).1 (completedIntegralTrace M z).2
    (completedIntegralTrace N w).1 (completedIntegralTrace N w).2

theorem completed_pairing_mellin (M : ℕ) (z w : ℂ)
    (hz : 0 < (operatorHeightParameter z).re) (hw : 0 < (operatorHeightParameter w).re) :
    completedIntegralPairing M M z w =
      canonicalC3BracketTfvdCompletedWronskianReadout M z w := by
  unfold completedIntegralPairing
  rw [completed_trace_mellin M z hz, completed_trace_mellin M w hw]
  rfl

/-- Different cutoffs at the two independent arguments are allowed. -/
theorem completed_pairing_eq_original (M N : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    completedIntegralPairing M N z w =
      completedGreenWronskian completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z w := by
  have hz0 : 0 < (operatorHeightParameter z).re := hz.1
  have hw0 : 0 < (operatorHeightParameter w).re := hw.1
  unfold completedIntegralPairing
  rw [completed_trace_mellin M z hz0, completed_trace_mellin N w hw0,
    canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime M hz,
    canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime N hw]
  rfl

end
end CarryCompletedPairing
