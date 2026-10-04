import GeometryOfNumbers.Analysis.BaseTwoRawL2ReadoutObstruction

/-! # The derived whole-cell boundary return and the Hilbert interior limit

These limits specify the completed boundary datum independently of moments.
They do not package it as a Hilbert coordinate or identify it with vertical
TFVD trace data. No map `(x,ell(x))` is constructed.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal Topology
open Filter
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

/-- Total return from the first M complete C2 cells, before the incoming seed. -/
def baseTwoCompletedBoundaryPrefix (M : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range M,
    (criticalMaterialGradient t (baseTwoCellRightEdge k) -
      criticalMaterialGradient t (baseTwoCellLeftEdge k))

/-- Derived total edge return, not a free tail or a TFVD initial trace. -/
def baseTwoCompletedBoundaryValue (t : ℝ) : ℂ :=
  ∑' k : ℕ, (criticalMaterialGradient t (baseTwoCellRightEdge k) -
    criticalMaterialGradient t (baseTwoCellLeftEdge k))

theorem baseTwoCompletedBoundaryPrefix_eq_head_sub_seed (M : ℕ) (t : ℝ) :
    baseTwoCompletedBoundaryPrefix M t =
      baseTwoFiniteHead M t - criticalMaterialSample t 1 := by
  simp only [baseTwoCompletedBoundaryPrefix, ← baseTwoCriticalCenterCell_eq_gradientEdges]
  unfold baseTwoFiniteHead
  abel

/-- The boundary value is the norm-limit of exact whole-cell returns. -/
theorem baseTwoCompletedBoundaryPrefix_tendsto (t : ℝ) :
    Tendsto (fun M => baseTwoCompletedBoundaryPrefix M t) atTop
      (𝓝 (baseTwoCompletedBoundaryValue t)) := by
  simpa only [baseTwoCompletedBoundaryPrefix, baseTwoCompletedBoundaryValue,
    ← baseTwoCriticalCenterCell_eq_gradientEdges] using
      (summable_baseTwoCriticalCenterCell t).hasSum.tendsto_sum_nat

theorem baseTwoCompletedBoundaryValue_eq_readout_sub_seed (t : ℝ) :
    baseTwoCompletedBoundaryValue t =
      baseTwoCompletedUndressedReadout (baseTwoCompletedUndressedState t) -
        criticalMaterialSample t 1 := by
  rw [baseTwoCompletedUndressedReadout_apply]
  simp only [baseTwoCompletedUndressedState, baseTwoCompletedMaterialGradient_apply]
  unfold baseTwoCompletedBoundaryValue
  abel

theorem baseTwoCompletedBoundaryValue_add_seed_eq_signal (t : ℝ) :
    criticalMaterialSample t 1 + baseTwoCompletedBoundaryValue t =
      baseTwoCriticalCompleteSignal t := by
  rw [baseTwoCompletedBoundaryValue_eq_readout_sub_seed,
    baseTwoCompletedUndressedReadout_eq_signal]
  abel

/-- Ordinary finite material-coordinate truncation, not a vertical-depth chart. -/
def baseTwoCompletedMaterialInteriorPrefix (N : ℕ) (t : ℝ) : MaterialEdgeL2 :=
  ∑ j ∈ Finset.range N, lp.single 2 j (criticalMaterialGradient t j)

theorem baseTwoCompletedMaterialInteriorPrefix_tendsto (t : ℝ) :
    Tendsto (fun N => baseTwoCompletedMaterialInteriorPrefix N t) atTop
      (𝓝 (baseTwoCompletedMaterialGradientL2 t)) := by
  simpa only [baseTwoCompletedMaterialInteriorPrefix,
    baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply] using
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        (baseTwoCompletedMaterialGradientL2 t)).tendsto_sum_nat

end GeometryOfNumbers.Analysis.BaseTwoCompletion
