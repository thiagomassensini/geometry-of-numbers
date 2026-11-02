import DirectBound
import TenTrial

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction
open CarryMaterialVariation CarrySummableRadial CarryIntegralCertificate NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option maxRecDepth 65536

theorem ten_pair_constants_bounded (r s : ℕ) (hr : r ∈ tenOrders) (hs : s ∈ tenOrders) :
    pairConstant r s ≤ (10:ℝ)^10 := by
  have hr' : r<5 := Finset.mem_range.mp hr
  have hs' : s<5 := Finset.mem_range.mp hs
  interval_cases r <;> interval_cases s <;>
    norm_num [pairConstant,oddFilterBudget,oddFilterCoefficient,nativeOddBeta,
      spatialCorrection,CarrySpatialCorrection.slope,CarrySpatialCorrection.curvature,
      Finset.sum_range_succ,Finset.sum_range_zero,Complex.norm_real,Real.norm_eq_abs,Nat.choose]

theorem ten_trial_coefficient_bounded (r : ℕ) (hr : r ∈ tenOrders) :
    |trialCoefficient r| ≤ 1 := by
  have hr' : r<5 := Finset.mem_range.mp hr
  interval_cases r <;> norm_num [trialCoefficient]

theorem ten_trial_budget_bounded : familyConstant tenOrders trialCoefficient ≤ 25*(10:ℝ)^10 := by
  unfold familyConstant
  calc
    _ ≤ ∑ r ∈ tenOrders, ∑ s ∈ tenOrders, (10:ℝ)^10 := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      have hc : |trialCoefficient r*trialCoefficient s| ≤ 1 := by
        rw [abs_mul]
        have hm := mul_le_mul_of_nonneg_right (ten_trial_coefficient_bounded r hr) (abs_nonneg (trialCoefficient s))
        nlinarith [ten_trial_coefficient_bounded s hs]
      calc
        _ ≤ 1*pairConstant r s := mul_le_mul_of_nonneg_right hc (pair_constant_nonneg r s)
        _ ≤ (10:ℝ)^10 := by simpa using ten_pair_constants_bounded r s hr hs
    _ = _ := by norm_num [tenOrders,Finset.sum_range_succ,Finset.sum_range_zero]

def tenAnchorIndex : ℕ := 10^22-1

theorem ten_anchor_step : radialFourSourceStep tenAnchorIndex=1/(10:ℝ)^22 := by
  norm_num [radialFourSourceStep,tenAnchorIndex]

theorem ten_anchor_cutoff : oddGridCutoff tenOrders ≤ tenAnchorIndex := by
  have hcut : oddGridCutoff tenOrders=40 := by decide +kernel
  rw [hcut]
  norm_num [tenAnchorIndex]

/-- Direct finite-scale source value, with the exact same physical state,
and no positivity premise on the critical Schur pivot. -/
theorem ten_trial_finite_source_lower : (6/(10:ℝ)^30) <
    fullEnergy tenAnchorIndex (finiteOddJetSource tenOrders trialCoefficient tenAnchorIndex) := by
  have he := finite_energy_direct_error tenOrders trialCoefficient tenAnchorIndex ten_anchor_cutoff
  have hh := rational_trial_head_lower
  have hb := ten_trial_budget_bounded
  rw [ten_anchor_step] at he
  have hl := (abs_le.mp he).1
  have hm := mul_le_mul_of_nonneg_left hb (show (0:ℝ)≤(1/(10:ℝ)^22)^2 by positivity)
  have hn : (6/(10:ℝ)^30)+(25*(10:ℝ)^10)*(1/(10:ℝ)^22)^2 < 7/(10:ℝ)^30 := by norm_num
  nlinarith

theorem ten_trial_tail_budget : familyConstant tenOrders trialCoefficient*
    (radialFourSourceStep tenAnchorIndex)^2 ≤ 25/(10:ℝ)^34 := by
  have hb := ten_trial_budget_bounded
  rw [ten_anchor_step]
  have hm := mul_le_mul_of_nonneg_right hb (show (0:ℝ)≤(1/(10:ℝ)^22)^2 by positivity)
  have hn : (25*(10:ℝ)^10)*(1/(10:ℝ)^22)^2=25/(10:ℝ)^34 := by norm_num
  linarith

theorem ten_trial_anchor_dominates_tail :
    familyConstant tenOrders trialCoefficient*(radialFourSourceStep tenAnchorIndex)^2 <
      fullEnergy tenAnchorIndex (finiteOddJetSource tenOrders trialCoefficient tenAnchorIndex) := by
  have h1 := ten_trial_finite_source_lower
  have h2 := ten_trial_tail_budget
  have h3 : (25/(10:ℝ)^34) < 6/(10:ℝ)^30 := by norm_num
  linarith

end
end CarryDirectAnchor
