import GreenPortCalibration

namespace CarryGreenProvenance
open CarryFourLeg CarryCameraTail CarryMaterialTheta CarrySelfAdjointOperator
open CPFormal.Analytic.Cp NativeCarryC3Crosswalk NativeCarrySpectralWeyl.Boundary
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- One of the TWO boundary cells, still with its four named leg swaps.
The third Green residue is kept separately in heatBlockProvenance. -/
def heatCellProvenance (M : ℕ) (z w : ℂ) (m : Fin M) (r : Fin 2) :
    TfvdSameSGreenLegChannels :=
  let a := heatMixedLegs M z w
  let d := materialGreenPort (M*3) w
  let e := materialGreenPort (M*3) (reflectedParameter z)
  let i : Fin (M*3) := finProdFinEquiv (m, (r.castLE (by omega) : Fin 3))
  tfvdPairGreenLegChannels (a.left (m,r)) (a.right (m,r))
    (a.jetLeft (m,r)) (a.jetRight (m,r))
    (d.1 i) (d.2 i) (e.1 i) (e.2 i)

/-- The entire three-residue block, including its dormant Green term.
No difference between global totals defines any of these fields. -/
def heatBlockProvenance (M : ℕ) (z w : ℂ) (m : Fin M) :
    TfvdSameSGreenProvenanceChannels where
  visibleLegs := heatCellProvenance M z w m 0
  dormantLegs := heatCellProvenance M z w m 1
  dormantGreenCompensation :=
    -finiteC3GreenPortEdge (materialGreenPort (M*3) w)
      (materialGreenPort (M*3) (reflectedParameter z)) (finProdFinEquiv (m,2))

def originalBlockProvenance (M : ℕ) (z w : ℂ) (m : Fin M) :
    TfvdSameSGreenProvenanceChannels :=
  let pair := canonicalMixedBoundaryResidualPair tfvdHaarScale (fun _ => 1) z w
  finiteC3EnrichedTfvdBlockGreenProvenance M tfvdHaarScale (fun _ => 1) pair
    (finiteC3EnrichedTfvdPairTransport M tfvdHaarScale (fun _ => 1) w pair)
    (finiteC3EnrichedTfvdPairTransport M tfvdHaarScale (fun _ => 1)
      (reflectedParameter z)
      (canonicalBoundaryResidualPair tfvdHaarScale (fun _ => 1) (reflectedParameter z))) m

theorem heat_cell_address_calibration (M : ℕ) (z w : ℂ) (m : Fin M) (r : Fin 2)
    (hz : 0 < z.re) (hw : 0 < w.re) :
    heatCellProvenance M z w m r =
      let d := materialGreenPort (M*3) w
      let e := materialGreenPort (M*3) (reflectedParameter z)
      let i : Fin (M*3) := finProdFinEquiv (m, (r.castLE (by omega) : Fin 3))
      tfvdPairGreenLegChannels
        (positiveDirichletGradient w (3*m.val+r.val))
        (positiveDirichletGradient w (3*m.val+r.val+1))
        (positiveLogDirichletGradient z (3*m.val+r.val))
        (positiveLogDirichletGradient z (3*m.val+r.val+1))
        (d.1 i) (d.2 i) (e.1 i) (e.2 i) := by
  unfold heatCellProvenance
  rw [heat_mixed_legs_calibration M hz hw]
  rfl

/-- Whole record equality, BEFORE the .total readout: eight distinct leg
fields plus the third-residue compensation. The strip bound on z is needed
for the reflected Mellin integral, not for the original algebraic ledger. -/
theorem block_provenance_mellin (M : ℕ) (m : Fin M) {z w : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) (hw : 0 < w.re) :
    heatBlockProvenance M z w m = originalBlockProvenance M z w m := by
  unfold heatBlockProvenance
  rw [heat_cell_address_calibration M z w m 0 hz hw,
    heat_cell_address_calibration M z w m 1 hz hw,
    material_green_port_eq _ hw, material_green_port_eq _ (reflected_re_pos hz1)]
  unfold originalBlockProvenance finiteC3EnrichedTfvdBlockGreenProvenance
  dsimp only
  rw [mixed_value_decode tfvdHaarScale_ne_zero (fun _ => 1) (by simp),
    mixed_log_decode tfvdHaarScale_ne_zero (fun _ => 1) (by simp),
    mixed_direct_green_port, reflected_green_port]
  rfl

theorem visible_legs_mellin (M : ℕ) (m : Fin M) {z w : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) (hw : 0 < w.re) :
    (heatBlockProvenance M z w m).visibleLegs =
      (originalBlockProvenance M z w m).visibleLegs :=
  congrArg TfvdSameSGreenProvenanceChannels.visibleLegs
    (block_provenance_mellin M m hz hz1 hw)

theorem dormant_legs_mellin (M : ℕ) (m : Fin M) {z w : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) (hw : 0 < w.re) :
    (heatBlockProvenance M z w m).dormantLegs =
      (originalBlockProvenance M z w m).dormantLegs :=
  congrArg TfvdSameSGreenProvenanceChannels.dormantLegs
    (block_provenance_mellin M m hz hz1 hw)

theorem dormant_compensation_mellin (M : ℕ) (m : Fin M) {z w : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) (hw : 0 < w.re) :
    (heatBlockProvenance M z w m).dormantGreenCompensation =
      (originalBlockProvenance M z w m).dormantGreenCompensation :=
  congrArg TfvdSameSGreenProvenanceChannels.dormantGreenCompensation
    (block_provenance_mellin M m hz hz1 hw)

/-- Summation is allowed only after block_provenance_mellin. -/
def heatGreenProvenance (M : ℕ) (z w : ℂ) : ℂ :=
  ∑ m : Fin M, (heatBlockProvenance M z w m).total

theorem heat_green_eq_original_ledger (M : ℕ) {z w : ℂ}
    (hz : 0 < z.re) (hz1 : z.re < 1) (hw : 0 < w.re) :
    heatGreenProvenance M z w =
      (canonicalNativePolarizedTfvdGreenLedger M z w).greenProvenance := by
  unfold heatGreenProvenance
  simp_rw [block_provenance_mellin M _ hz hz1 hw]
  rfl

end
end CarryGreenProvenance
