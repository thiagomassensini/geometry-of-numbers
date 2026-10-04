import GeometryOfNumbers.Analysis.BaseTwoCompletedBoundaryLimit
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Completed material interior with an explicit geometric boundary

The standard Hilbert product stores seed, material-edge interior, and the
whole-cell return derived by geometric prefix convergence. It does not extend
the raw edge readout to ℓ², nor identify material edges with vertical depth.
-/
noncomputable section
open scoped BigOperators lp ENNReal Topology
open Filter
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

/-- Standard Hilbert sum: seed ⊕ (material-edge interior ⊕ whole-cell return). -/
abbrev BaseTwoCompletedBoundaryHilbertCarrier : Type :=
  WithLp 2 (ℂ × WithLp 2 (MaterialEdgeL2 × ℂ))

/-- Finite material interior and finite complete-cell return have separate
geometric meanings, even when parameterized by the same natural cutoff. -/
def baseTwoCompletedBoundaryHilbertPrefixState (N : ℕ) (t : ℝ) :
    BaseTwoCompletedBoundaryHilbertCarrier :=
  WithLp.toLp 2 (criticalMaterialSample t 1,
    WithLp.toLp 2 (baseTwoCompletedMaterialInteriorPrefix N t,
      baseTwoCompletedBoundaryPrefix N t))

/-- The return component comes from the already derived geometric return sum,
not from defining the complete signal minus the seed. -/
def baseTwoCompletedBoundaryHilbertState (t : ℝ) :
    BaseTwoCompletedBoundaryHilbertCarrier :=
  WithLp.toLp 2 (criticalMaterialSample t 1,
    WithLp.toLp 2 (baseTwoCompletedMaterialGradientL2 t,
      baseTwoCompletedBoundaryValue t))

@[simp] theorem baseTwoCompletedBoundaryHilbertState_seed (t : ℝ) :
    (baseTwoCompletedBoundaryHilbertState t).fst = criticalMaterialSample t 1 := rfl

@[simp] theorem baseTwoCompletedBoundaryHilbertState_interior (t : ℝ) :
    (baseTwoCompletedBoundaryHilbertState t).snd.fst =
      baseTwoCompletedMaterialGradientL2 t := rfl

@[simp] theorem baseTwoCompletedBoundaryHilbertState_boundary (t : ℝ) :
    (baseTwoCompletedBoundaryHilbertState t).snd.snd =
      baseTwoCompletedBoundaryValue t := rfl

/-- Convergence in the standard product Hilbert norm, not just coordinatewise. -/
theorem baseTwoCompletedBoundaryHilbertPrefixState_tendsto (t : ℝ) :
    Tendsto (fun N => baseTwoCompletedBoundaryHilbertPrefixState N t) atTop
      (𝓝 (baseTwoCompletedBoundaryHilbertState t)) := by
  have hi := (baseTwoCompletedMaterialInteriorPrefix_tendsto t).prodMk_nhds
    (baseTwoCompletedBoundaryPrefix_tendsto t)
  have hp := (WithLp.prod_continuous_toLp 2 MaterialEdgeL2 ℂ).continuousAt.tendsto.comp hi
  have hs := (tendsto_const_nhds (x := criticalMaterialSample t 1)).prodMk_nhds hp
  exact (WithLp.prod_continuous_toLp 2 ℂ
    (WithLp 2 (MaterialEdgeL2 × ℂ))).continuousAt.tendsto.comp hs

/-- The bounded readout only reads seed and explicit return; it ignores interior. -/
def baseTwoCompletedBoundaryHilbertReadout :
    BaseTwoCompletedBoundaryHilbertCarrier →L[ℂ] ℂ :=
  WithLp.fstL 2 ℂ ℂ (WithLp 2 (MaterialEdgeL2 × ℂ)) +
    (WithLp.sndL 2 ℂ MaterialEdgeL2 ℂ).comp
      (WithLp.sndL 2 ℂ ℂ (WithLp 2 (MaterialEdgeL2 × ℂ)))

@[simp] theorem baseTwoCompletedBoundaryHilbertReadout_apply
    (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    baseTwoCompletedBoundaryHilbertReadout y = y.fst + y.snd.snd := rfl

/-- Exact synthesis through the derived boundary component. -/
theorem baseTwoCompletedBoundaryHilbertReadout_eq_signal (t : ℝ) :
    baseTwoCompletedBoundaryHilbertReadout (baseTwoCompletedBoundaryHilbertState t) =
      baseTwoCriticalCompleteSignal t :=
  baseTwoCompletedBoundaryValue_add_seed_eq_signal t

/-- The Hilbert and Banach realizations have the same observable. This is not
an identification or an isometry of their carriers. -/
theorem baseTwoCompletedBoundaryHilbertReadout_eq_banachReadout (t : ℝ) :
    baseTwoCompletedBoundaryHilbertReadout (baseTwoCompletedBoundaryHilbertState t) =
      baseTwoCompletedUndressedReadout (baseTwoCompletedUndressedState t) := by
  rw [baseTwoCompletedBoundaryHilbertReadout_eq_signal,
    baseTwoCompletedUndressedReadout_eq_signal]

/-- Finite readout is exactly the geometric finite head. -/
theorem baseTwoCompletedBoundaryHilbertPrefixState_readout (N : ℕ) (t : ℝ) :
    baseTwoCompletedBoundaryHilbertReadout
      (baseTwoCompletedBoundaryHilbertPrefixState N t) = baseTwoFiniteHead N t := by
  change criticalMaterialSample t 1 + baseTwoCompletedBoundaryPrefix N t = _
  rw [baseTwoCompletedBoundaryPrefix_eq_head_sub_seed]
  abel

/-- The bounded readout also carries Hilbert prefix convergence to the signal. -/
theorem baseTwoCompletedBoundaryHilbertPrefixState_readout_tendsto (t : ℝ) :
    Tendsto (fun N => baseTwoCompletedBoundaryHilbertReadout
      (baseTwoCompletedBoundaryHilbertPrefixState N t)) atTop
      (𝓝 (baseTwoCriticalCompleteSignal t)) := by
  rw [← baseTwoCompletedBoundaryHilbertReadout_eq_signal t]
  exact baseTwoCompletedBoundaryHilbertReadout.continuous.continuousAt.tendsto.comp
    (baseTwoCompletedBoundaryHilbertPrefixState_tendsto t)

end GeometryOfNumbers.Analysis.BaseTwoCompletion
