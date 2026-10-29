import TenDirectAnchor

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial CarryBoundaryReconstruction
open CarryMaterialVariation CarrySummableRadial CarryIntegralCertificate NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem ten_step_after_anchor (k : ℕ) (hk : tenAnchorIndex ≤ k) :
    radialFourSourceStep k ≤ 1/(10:ℝ)^22 := by
  have hn : (10:ℝ)^22 ≤ (k:ℝ)+1 := by
    exact_mod_cast (show (10:ℕ)^22≤k+1 by unfold tenAnchorIndex at hk; omega)
  unfold radialFourSourceStep
  rw [one_div]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hn

theorem ten_trial_source_lower_after_anchor (k : ℕ) (hk : tenAnchorIndex ≤ k) :
    (6/(10:ℝ)^30) < fullEnergy k (finiteOddJetSource tenOrders trialCoefficient k) := by
  have he := finite_energy_direct_error tenOrders trialCoefficient k (ten_anchor_cutoff.trans hk)
  have hh := rational_trial_head_lower
  have hb := ten_trial_budget_bounded
  have hp := radial_step_positive k
  have hs := ten_step_after_anchor k hk
  have hs2 : (radialFourSourceStep k)^2 ≤ (1/(10:ℝ)^22)^2 := by nlinarith [sq_nonneg (radialFourSourceStep k)]
  have hB := family_constant_nonneg tenOrders trialCoefficient
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg (radialFourSourceStep k))
  have hn := mul_le_mul_of_nonneg_left hs2 (show (0:ℝ) ≤ 25*(10:ℝ)^10 by positivity)
  have hpw : (6/(10:ℝ)^30)+(25*(10:ℝ)^10)*(1/(10:ℝ)^22)^2 < 7/(10:ℝ)^30 := by norm_num
  have hl := (abs_le.mp he).1
  nlinarith

theorem ten_trial_tail_budget_after_anchor (k : ℕ) (hk : tenAnchorIndex ≤ k) :
    familyConstant tenOrders trialCoefficient*(radialFourSourceStep k)^2 ≤ 25/(10:ℝ)^34 := by
  have hb := ten_trial_budget_bounded
  have hp := radial_step_positive k
  have hs := ten_step_after_anchor k hk
  have hs2 : (radialFourSourceStep k)^2 ≤ (1/(10:ℝ)^22)^2 := by nlinarith [sq_nonneg (radialFourSourceStep k)]
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg (radialFourSourceStep k))
  have hn := mul_le_mul_of_nonneg_left hs2 (show (0:ℝ) ≤ 25*(10:ℝ)^10 by positivity)
  have hc : (25*(10:ℝ)^10)*(1/(10:ℝ)^22)^2 = 25/(10:ℝ)^34 := by norm_num
  nlinarith

end
end CarryDirectAnchor
