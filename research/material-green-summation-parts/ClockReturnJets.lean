import CellReturnJets

/-! The second original return channel receives the same all-order ℓ¹
jet/tail treatment. This is regularity of the actual log-gradient curve,
not membership of the source in powers of an unbounded material clock. -/
namespace CarryMaterialParts
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

theorem material_clock_l1_analytic (t : ℝ) : AnalyticAt ℝ baseTwoCompletedMaterialClockL1 t := by
  have he : baseTwoCompletedMaterialClockL1 =
      fun u => Complex.I • deriv baseTwoCompletedMaterialGradient u := by
    funext u
    rw [(baseTwoCompletedMaterialGradient_hasDerivAt_clock u).deriv, smul_smul]
    simp
  rw [he]
  exact (analyticAt_const (v := (Complex.I:ℂ))).smul (material_l1_analytic t).deriv

theorem cellReturnReadout_clock_source (t : ℝ) :
    cellReturnReadout (baseTwoCompletedMaterialClockL1 t) = carryValveKappa t := by
  rw [cellReturnReadout_apply]
  rfl

def materialClockL1Jet (m : ℕ) : MaterialGradientL1 :=
  l1JetShift m baseTwoCompletedMaterialClockL1 0

def clockCellJet (m k : ℕ) : ℂ :=
  materialClockL1Jet m (baseTwoCellRightEdge k)-materialClockL1Jet m (baseTwoCellLeftEdge k)

theorem clock_return_jet_readout (m : ℕ) :
    carryScalarJetShift m carryValveKappa 0 = cellReturnReadout (materialClockL1Jet m) := by
  have he : carryValveKappa = (cellReturnReadout.restrictScalars ℝ) ∘ baseTwoCompletedMaterialClockL1 := by
    funext t
    exact (cellReturnReadout_clock_source t).symm
  rw [he, map_l1_jets _ (material_clock_l1_analytic 0)]
  rfl

theorem clock_cell_jet_norm_summable (m : ℕ) : Summable (fun k => ‖clockCellJet m k‖) := by
  have hs : Summable (fun n => ‖materialClockL1Jet m n‖) := by simpa using (materialClockL1Jet m).property.summable
  have hr := hs.comp_injective (show Function.Injective baseTwoCellRightEdge by intro i j h; simp at h; omega)
  have hl := hs.comp_injective (show Function.Injective baseTwoCellLeftEdge by intro i j h; simp at h; omega)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_sub_le _ _) (hr.add hl)

theorem clock_return_jet_cells (m : ℕ) :
    carryScalarJetShift m carryValveKappa 0 = ∑' k, clockCellJet m k := by
  rw [clock_return_jet_readout, cellReturnReadout_apply]
  rfl

/-- The summand is the original clocked TFVD cell, with its two material
addresses and actual complex phase, in every fixed Taylor order. -/
theorem clock_cell_jet_source (eta : ℝ) (heta : eta ≠ 0) (m k : ℕ) :
    clockCellJet m k = carryScalarJetShift m
      (fun t => carryValveCell eta (completedBoundaryTransportedClock (carryValveSource t)) k) 0 := by
  have he : (fun t => carryValveCell eta (completedBoundaryTransportedClock (carryValveSource t)) k) =
      (cellJetCoordinate k).restrictScalars ℝ ∘ baseTwoCompletedMaterialClockL1 := by
    funext t
    rw [carryValveCell_eq eta heta]
    rfl
  rw [he, map_l1_jets _ (material_clock_l1_analytic 0)]
  rfl

theorem clock_return_jet_head_tail (m M : ℕ) :
    carryScalarJetShift m carryValveKappa 0 =
      (∑ k ∈ Finset.range M, clockCellJet m k)+∑' k, clockCellJet m (k+M) := by
  rw [clock_return_jet_cells]
  exact ((clock_cell_jet_norm_summable m).of_norm.sum_add_tsum_nat_add M).symm

theorem clock_return_jet_tail_bound (m M : ℕ) :
    ‖carryScalarJetShift m carryValveKappa 0-(∑ k ∈ Finset.range M, clockCellJet m k)‖ ≤
      ∑' k, ‖clockCellJet m (k+M)‖ := by
  rw [clock_return_jet_head_tail m M, add_sub_cancel_left]
  exact norm_tsum_le_tsum_norm ((clock_cell_jet_norm_summable m).comp_injective
    (by intro i j h; exact Nat.add_right_cancel h))

theorem clock_return_jet_tail_tendsto (m : ℕ) :
    Tendsto (fun M => ∑' k, clockCellJet m (k+M)) atTop (nhds 0) :=
  tendsto_sum_nat_add (clockCellJet m)

theorem clock_return_jet_norm_tail_tendsto (m : ℕ) :
    Tendsto (fun M => ∑' k, ‖clockCellJet m (k+M)‖) atTop (nhds 0) :=
  tendsto_sum_nat_add (fun k => ‖clockCellJet m k‖)

end
end CarryMaterialParts
