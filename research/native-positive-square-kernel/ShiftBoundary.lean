import CarrySelfAdjointOperator.NativeCauchyLaguerreShift

namespace CarryPositiveSquare
open CarrySelfAdjointOperator.NativeLaguerre CPFormal.Analytic.Cp
open scoped InnerProductSpace ComplexConjugate lp
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The zeroth coordinate of the OLD isometry; no moment calibrates it. -/
def shiftBoundary : PhysicalCauchySpace →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 0).comp cauchyLaguerreIsometry.toContinuousLinearMap

/-- Full polarized boundary loss in the original Cauchy metric. -/
theorem physical_shift_boundary (x y : PhysicalCauchySpace) :
    inner ℂ x y-inner ℂ (physicalCauchyShift 1 x) (physicalCauchyShift 1 y) =
      conj (shiftBoundary x)*shiftBoundary y := by
  have hs := (lp.summable_inner (𝕜 := ℂ) (cauchyLaguerreIsometry x) (cauchyLaguerreIsometry y)).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hs
  rw [← cauchyLaguerreIsometry.inner_map_map x y,
    ← cauchyLaguerreIsometry.inner_map_map (physicalCauchyShift 1 x) (physicalCauchyShift 1 y),
    physicalCauchyShift_intertwines, physicalCauchyShift_intertwines, lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [carryVerticalL2BackwardShift_apply]
  rw [← hs]
  simp only [shiftBoundary, ContinuousLinearMap.comp_apply, RCLike.inner_apply]
  rw [add_sub_cancel_right]
  change (cauchyLaguerreIsometry y 0)*conj (cauchyLaguerreIsometry x 0) =
    conj (cauchyLaguerreIsometry x 0)*(cauchyLaguerreIsometry y 0)
  ring

/-- Exact adjoint-square calculation; the complement is a single boundary
functional, rather than the requested full completed-native kernel. -/
theorem physical_shift_square :
    (physicalCauchyShift 1).adjoint.comp (physicalCauchyShift 1) =
      1-shiftBoundary.adjoint.comp shiftBoundary := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  change _ = inner ℂ (x-shiftBoundary.adjoint (shiftBoundary x)) y
  rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
  have hh := physical_shift_boundary x y
  simp only [RCLike.inner_apply] at ⊢
  rw [mul_comm (shiftBoundary y)]
  linear_combination -hh

end
end CarryPositiveSquare
