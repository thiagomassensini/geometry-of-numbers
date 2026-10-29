import SixSign
import RadialRegularity
import SquaredStepBudget

namespace CarryEffectiveRadial
open CarrySelfAdjointOperator CarryMaterialVariation CarryIntegralCertificate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

def budgetStep : ℝ := 1/(10:ℝ)^20
def budgetIndex : ℕ := 10^20-1

theorem budget_step_positive : 0<budgetStep := by norm_num [budgetStep]
theorem budget_step_small : budgetStep<1/1000 := by norm_num [budgetStep]

def unitBox : Box := .finite (-(10^60)) (10^60)
def smallCorrectionBox : Box := .finite (-(10^57)) (10^57)

theorem critical_sizes : |sixU|≤1 ∧ |sixV|≤1 ∧ |sixCorrection sixU sixV|≤1/1000 := by
  have hu := mem_of_contained source_box_membership.2.1
    (show sixUBox.contained unitBox=true by decide +kernel)
  have hv := mem_of_contained source_box_membership.2.2.1
    (show sixVBox.contained unitBox=true by decide +kernel)
  have hc := mem_of_contained source_box_membership.2.2.2
    (show sixCorrectionBox.contained smallCorrectionBox=true by decide +kernel)
  norm_num [unitBox,smallCorrectionBox,Box.Mem,intervalScale] at hu hv hc
  exact ⟨abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩,
    abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩,
    abs_le.mpr ⟨by linarith [hc.1],by linarith [hc.2]⟩⟩

def sixLimitBox : Box :=
  let t0 := logMomentBox 5
  let t1 := ((Box.point 2).mul sixUBox).mul (logMomentBox 4)
  let t2 := ((sixUBox.pow 2).add ((Box.point 2).mul sixVBox)).mul (logMomentBox 3)
  let t3 := (((Box.point 2).mul sixUBox).mul sixVBox).mul (logMomentBox 2)
  let t4 := (sixVBox.pow 2).mul (logMomentBox 1)
  (Box.point 2).mul ((((t0.add t1).add t2).add t3).add t4)
def stepBox : Box := Box.rat 1 (10^20)
def anchorHeadBox : Box := sixLimitBox.add (sixCorrectionBox.mul (stepBox.pow 2))

/-- Direct source polynomial at the chosen finite radial scale. The sign of
its limiting Schur residual is not an input. -/
theorem anchor_head_membership : anchorHeadBox.Mem
    (sixLimit sixU sixV+sixCorrection sixU sixV*budgetStep^2) := by
  have h1 := mem_logMomentBox material_theta_integral_input 1
  have h2 := mem_logMomentBox material_theta_integral_input 2
  have h3 := mem_logMomentBox material_theta_integral_input 3
  have h4 := mem_logMomentBox material_theta_integral_input 4
  have h5 := mem_logMomentBox material_theta_integral_input 5
  have hu := source_box_membership.2.1
  have hv := source_box_membership.2.2.1
  have hl := mem_mul (mem_point 2) (mem_add (mem_add (mem_add (mem_add h5
    (mem_mul (mem_mul (mem_point 2) hu) h4))
    (mem_mul (mem_add (mem_pow hu 2) (mem_mul (mem_point 2) hv)) h3))
    (mem_mul (mem_mul (mem_mul (mem_point 2) hu) hv) h2)) (mem_mul (mem_pow hv 2) h1))
  have hstep : stepBox.Mem budgetStep := by
    convert mem_rat 1 (10^20) using 1 <;> norm_num [stepBox,budgetStep]
  have hh := mem_add hl (mem_mul source_box_membership.2.2.2 (mem_pow hstep 2))
  convert hh using 1
  all_goals rfl

theorem anchor_head_lower : (15/(10:ℝ)^17) ≤
    sixLimit sixU sixV+sixCorrection sixU sixV*budgetStep^2 := by
  have hm := mem_of_contained anchor_head_membership
    (show anchorHeadBox.contained (.finite (15*10^43) (2*10^44))=true by decide +kernel)
  norm_num [Box.Mem,intervalScale] at hm
  linarith [hm.1]

end
end CarryEffectiveRadial
