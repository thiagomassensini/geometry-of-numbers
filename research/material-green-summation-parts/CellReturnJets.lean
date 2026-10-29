import ReturnTailParts

/-! Strong analytic jets in the ORIGINAL absolutely summable material-gradient
space. The scalar global return is taken only through its existing bounded
ℓ¹ readout. No higher unbounded-clock domain and no moment sign is assumed. -/
namespace CarryMaterialParts
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

theorem material_l1_analytic (t : ℝ) : AnalyticAt ℝ baseTwoCompletedMaterialGradient t := by
  have hC : AnalyticAt ℂ (baseTwoComplexMaterialGradientLp 1) (t:ℂ) :=
    (baseTwoComplexMaterialGradientLp_differentiableOn_ball 1 t).analyticAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))
  have hR := (hC.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)
  have he : baseTwoComplexMaterialGradientLp 1 ∘ Complex.ofReal = baseTwoCompletedMaterialGradient := by
    funext u
    exact baseTwoComplexMaterialGradientLp_ofReal 1 (by norm_num) u _ (fun _ => rfl)
  simpa only [Complex.ofRealCLM_apply, he] using hR

def l1JetShift (n : ℕ) (f : ℝ → MaterialGradientL1) : ℝ → MaterialGradientL1 :=
  (fun g : ℝ → MaterialGradientL1 => dslope g 0)^[n] f

theorem l1JetShift_succ (n : ℕ) (f : ℝ → MaterialGradientL1) :
    l1JetShift (n+1) f = dslope (l1JetShift n f) 0 := Function.iterate_succ_apply' _ _ _

theorem l1JetShift_analytic {f : ℝ → MaterialGradientL1} (hf : AnalyticAt ℝ f 0) (n : ℕ) :
    AnalyticAt ℝ (l1JetShift n f) 0 := by
  obtain ⟨p,hp⟩ := hf
  exact (hp.has_fpower_series_iterate_dslope_fslope n).analyticAt

theorem map_l1_jets (L : MaterialGradientL1 →L[ℝ] ℂ) {f : ℝ → MaterialGradientL1}
    (hf : AnalyticAt ℝ f 0) (n : ℕ) :
    carryScalarJetShift n (L ∘ f) = fun t => L (l1JetShift n f t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [carryScalarJetShift_succ, ih, l1JetShift_succ]
    funext t
    exact L.dslope_comp (l1JetShift n f) 0 t (fun _ => (l1JetShift_analytic hf n).differentiableAt)

/-- Reuse the original ℓ¹ readout with a zero seed, not a sum on ℓ². -/
def cellReturnReadout : MaterialGradientL1 →L[ℂ] ℂ :=
  baseTwoCompletedUndressedReadout.comp (ContinuousLinearMap.inr ℂ ℂ MaterialGradientL1)

theorem cellReturnReadout_apply (g : MaterialGradientL1) :
    cellReturnReadout g = ∑' k, (g (baseTwoCellRightEdge k)-g (baseTwoCellLeftEdge k)) := by
  simp only [cellReturnReadout, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    baseTwoCompletedUndressedReadout_apply, zero_add]

theorem cellReturnReadout_source (t : ℝ) :
    cellReturnReadout (baseTwoCompletedMaterialGradient t) = baseTwoCompletedBoundaryValue t := by
  rw [cellReturnReadout_apply]
  have h := (baseTwoCompletedBoundaryHilbertState_mem_clockDomain t).1
  exact h.tsum_eq

def materialL1Jet (m : ℕ) : MaterialGradientL1 := l1JetShift m baseTwoCompletedMaterialGradient 0

def cellJet (m k : ℕ) : ℂ :=
  materialL1Jet m (baseTwoCellRightEdge k)-materialL1Jet m (baseTwoCellLeftEdge k)

theorem return_jet_readout (m : ℕ) :
    carryScalarJetShift m baseTwoCompletedBoundaryValue 0 = cellReturnReadout (materialL1Jet m) := by
  have he : baseTwoCompletedBoundaryValue =
      (cellReturnReadout.restrictScalars ℝ) ∘ baseTwoCompletedMaterialGradient := by
    funext t
    exact (cellReturnReadout_source t).symm
  rw [he, map_l1_jets _ (material_l1_analytic 0)]
  rfl

theorem cell_jet_norm_summable (m : ℕ) : Summable (fun k => ‖cellJet m k‖) := by
  have hs : Summable (fun n => ‖materialL1Jet m n‖) := by simpa using (materialL1Jet m).property.summable
  have hr := hs.comp_injective (show Function.Injective baseTwoCellRightEdge by intro i j h; simp at h; omega)
  have hl := hs.comp_injective (show Function.Injective baseTwoCellLeftEdge by intro i j h; simp at h; omega)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_sub_le _ _) (hr.add hl)

/-- Absolute convergence and an exact all-order source identity. -/
theorem return_jet_cells (m : ℕ) :
    carryScalarJetShift m baseTwoCompletedBoundaryValue 0 = ∑' k, cellJet m k := by
  rw [return_jet_readout, cellReturnReadout_apply]
  rfl

def cellJetCoordinate (k : ℕ) : MaterialGradientL1 →L[ℂ] ℂ :=
  lp.evalCLM ℂ (fun _ : ℕ => ℂ) 1 (baseTwoCellRightEdge k)-
    lp.evalCLM ℂ (fun _ : ℕ => ℂ) 1 (baseTwoCellLeftEdge k)

/-- Each summand is the actual Taylor jet of the original center/two-leg cell. -/
theorem cell_jet_source (m k : ℕ) :
    cellJet m k = carryScalarJetShift m (fun t => baseTwoCriticalCenterCell t k) 0 := by
  have he : (fun t => baseTwoCriticalCenterCell t k) =
      (cellJetCoordinate k).restrictScalars ℝ ∘ baseTwoCompletedMaterialGradient := by
    funext t
    rw [baseTwoCriticalCenterCell_eq_gradientEdges]
    rfl
  rw [he, map_l1_jets _ (material_l1_analytic 0)]
  rfl

/-- Exact head/tail at every fixed jet order, without recomputing moments
from a truncated source and without a limit/derivative interchange assumption. -/
theorem return_jet_head_tail (m M : ℕ) :
    carryScalarJetShift m baseTwoCompletedBoundaryValue 0 =
      (∑ k ∈ Finset.range M, cellJet m k)+∑' k, cellJet m (k+M) := by
  rw [return_jet_cells]
  exact ((cell_jet_norm_summable m).of_norm.sum_add_tsum_nat_add M).symm

theorem return_jet_tail_bound (m M : ℕ) :
    ‖carryScalarJetShift m baseTwoCompletedBoundaryValue 0-(∑ k ∈ Finset.range M, cellJet m k)‖ ≤
      ∑' k, ‖cellJet m (k+M)‖ := by
  rw [return_jet_head_tail m M, add_sub_cancel_left]
  exact norm_tsum_le_tsum_norm ((cell_jet_norm_summable m).comp_injective (by intro i j h; exact Nat.add_right_cancel h))

/-- Fixed m only: this theorem contains no uniform-in-order tail budget. -/
theorem return_jet_tail_tendsto (m : ℕ) :
    Tendsto (fun M => ∑' k, cellJet m (k+M)) atTop (nhds 0) :=
  tendsto_sum_nat_add (cellJet m)

theorem return_jet_norm_tail_tendsto (m : ℕ) :
    Tendsto (fun M => ∑' k, ‖cellJet m (k+M)‖) atTop (nhds 0) :=
  tendsto_sum_nat_add (fun k => ‖cellJet m k‖)

end
end CarryMaterialParts
