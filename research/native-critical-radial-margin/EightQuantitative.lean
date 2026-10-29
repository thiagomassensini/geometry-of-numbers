import EightMargin

namespace CarryCriticalRadialMargin
open CarrySelfAdjointOperator CarryCriticalTfvd CarryOddEnergy CarrySummableRadial CarryMaterialVariation
open CarryEffectiveRadial CarryBoundaryReconstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem eight_general_tail_explicit :
    familyConstant eightOrders eightCoefficients*(radialFourSourceStep budgetIndex)^2 ≤
      16/(10:ℝ)^31 := by
  have hb := eight_family_constant_bounded
  have hs : (radialFourSourceStep budgetIndex)^2=1/(10:ℝ)^40 := by
    rw [step_at_budget_index]
    norm_num [budgetStep]
  rw [hs]
  have hx := mul_le_mul_of_nonneg_right hb (show (0:ℝ)≤1/(10:ℝ)^40 by positivity)
  have he : (16*(10:ℝ)^9)*(1/(10:ℝ)^40)=16/(10:ℝ)^31 := by norm_num
  linarith

theorem eight_anchor_explicit_lower :
    9/(10:ℝ)^24 < fullEnergy budgetIndex (finiteOddJetSource eightOrders eightCoefficients budgetIndex) := by
  have ha := eight_anchor_error
  have hh := eight_head_strict_lower
  have hb := eight_general_tail_explicit
  have hl := (abs_le.mp ha).1
  have hn : (9/(10:ℝ)^24)+(16/(10:ℝ)^31)<1/(10:ℝ)^23 := by norm_num
  linarith

end
end CarryCriticalRadialMargin
