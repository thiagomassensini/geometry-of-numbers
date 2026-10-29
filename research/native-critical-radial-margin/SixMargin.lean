import SummableFamily
import SixRegression

namespace CarryCriticalRadialMargin
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction
open CarryMaterialVariation CarrySummableRadial NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 65536

/-- One explicit rational ceiling, uniform for the nine actual ordered
crosses of the original jets 1, 3, 5. -/
theorem six_pair_constants_bounded (r s : ℕ) (hr : r ∈ sixOrders) (hs : s ∈ sixOrders) :
    pairConstant r s ≤ (10:ℝ)^7 := by
  simp only [sixOrders, Finset.mem_insert, Finset.mem_singleton] at hr hs
  rcases hr with rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl <;>
    norm_num [pairConstant, oddFilterBudget, oddFilterCoefficient, nativeOddBeta,
      spatialCorrection, CarrySpatialCorrection.slope, CarrySpatialCorrection.curvature,
      Finset.sum_range_succ, Finset.sum_range_zero, Complex.norm_real, Real.norm_eq_abs,
      Nat.choose]

theorem six_coefficient_bounded (r : ℕ) (hr : r ∈ sixOrders) :
    |sixCoefficients sixU sixV r| ≤ 1 := by
  have h := critical_sizes
  simp only [sixOrders, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl
  · simpa [sixCoefficients] using h.2.1
  · simpa [sixCoefficients] using h.1
  · norm_num [sixCoefficients]

/-- Effective ceiling for the general PR #134 budget, with NO cancellation
of independent cross terms. -/
theorem six_family_constant_bounded :
    familyConstant sixOrders (sixCoefficients sixU sixV) ≤ 9*(10:ℝ)^7 := by
  unfold familyConstant
  calc
    _ ≤ ∑ r ∈ sixOrders, ∑ s ∈ sixOrders, (10:ℝ)^7 := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      have hc : |sixCoefficients sixU sixV r*sixCoefficients sixU sixV s| ≤ 1 := by
        rw [abs_mul]
        have hm := mul_le_mul_of_nonneg_right (six_coefficient_bounded r hr)
          (abs_nonneg (sixCoefficients sixU sixV s))
        nlinarith [six_coefficient_bounded s hs]
      calc
        _ ≤ 1*pairConstant r s := mul_le_mul_of_nonneg_right hc (pair_constant_nonneg r s)
        _ ≤ (10:ℝ)^7 := by simpa using six_pair_constants_bounded r s hr hs
    _ = _ := by norm_num [sixOrders, Finset.sum_insert, Finset.sum_singleton]

/-- The actual finite-scale balance beats the NEW general tail budget.
The independent lower enclosure is the original source integral result;
no limiting Schur sign enters this proof. -/
theorem six_anchor_beats_general_tail :
    familyConstant sixOrders (sixCoefficients sixU sixV)*(radialFourSourceStep budgetIndex)^2 <
      fullEnergy budgetIndex (finiteOddJetSource sixOrders (sixCoefficients sixU sixV) budgetIndex) := by
  have ha := six_effective_anchor_positive
  rw [six_physical_eq_twice_finite_energy] at ha
  have hb := six_family_constant_bounded
  have hstep : (radialFourSourceStep budgetIndex)^2=1/(10:ℝ)^40 := by
    rw [step_at_budget_index]
    norm_num [budgetStep]
  rw [hstep]
  have hc := mul_le_mul_of_nonneg_right hb (show (0:ℝ) ≤ 1/(10:ℝ)^40 by positivity)
  have hn : (9*(10:ℝ)^7)*(1/(10:ℝ)^40)<(1/(10:ℝ)^16)/2 := by norm_num
  linarith

end
end CarryCriticalRadialMargin
