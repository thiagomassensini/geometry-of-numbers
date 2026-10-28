import SixTaylor
import IntegralCertificate

namespace CarryMaterialVariation
open CarrySelfAdjointOperator CarryIntegralCertificate Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

def prefixDelta : ℝ := canonicalCompletedNativeLogDerivativeMoment 1*
  canonicalCompletedNativeLogDerivativeMoment 3-(canonicalCompletedNativeLogDerivativeMoment 2)^2
def uNumerator : ℝ := canonicalCompletedNativeLogDerivativeMoment 2*
  canonicalCompletedNativeLogDerivativeMoment 3-canonicalCompletedNativeLogDerivativeMoment 1*
    canonicalCompletedNativeLogDerivativeMoment 4
def vNumerator : ℝ := canonicalCompletedNativeLogDerivativeMoment 2*
  canonicalCompletedNativeLogDerivativeMoment 4-(canonicalCompletedNativeLogDerivativeMoment 3)^2
def sixU : ℝ := uNumerator/prefixDelta
def sixV : ℝ := vNumerator/prefixDelta

def deltaBox : Box := ((logMomentBox 1).mul (logMomentBox 3)).add (((logMomentBox 2).pow 2).neg)
def uNumeratorBox : Box := ((logMomentBox 2).mul (logMomentBox 3)).add
  (((logMomentBox 1).mul (logMomentBox 4)).neg)
def vNumeratorBox : Box := ((logMomentBox 2).mul (logMomentBox 4)).add
  (((logMomentBox 3).pow 2).neg)
def sixUBox : Box := uNumeratorBox.div deltaBox
def sixVBox : Box := vNumeratorBox.div deltaBox
def sixCorrectionBox : Box :=
  let a := ((Box.point (-10)).mul (sixVBox.pow 2)).mul (logMomentBox 2)
  let b := (((Box.point (-168)).mul sixUBox).mul sixVBox).mul (logMomentBox 3)
  let c := ((Box.point (-60)).mul ((sixUBox.pow 2).add ((Box.point 14).mul sixVBox))).mul (logMomentBox 4)
  let d := ((Box.point (-484)).mul sixUBox).mul (logMomentBox 5)
  let e := (Box.point (-182)).mul (logMomentBox 6)
  (((a.add b).add c).add d).add e

theorem delta_box_positive : deltaBox.positive=true := by decide +kernel
theorem six_correction_box_positive : sixCorrectionBox.positive=true := by decide +kernel

theorem source_box_membership : deltaBox.Mem prefixDelta ∧
    sixUBox.Mem sixU ∧ sixVBox.Mem sixV ∧ sixCorrectionBox.Mem (sixCorrection sixU sixV) := by
  have h1 := mem_logMomentBox material_theta_integral_input 1
  have h2 := mem_logMomentBox material_theta_integral_input 2
  have h3 := mem_logMomentBox material_theta_integral_input 3
  have h4 := mem_logMomentBox material_theta_integral_input 4
  have h5 := mem_logMomentBox material_theta_integral_input 5
  have h6 := mem_logMomentBox material_theta_integral_input 6
  have hd : deltaBox.Mem prefixDelta := by
    simpa only [deltaBox,prefixDelta,sub_eq_add_neg] using
      mem_add (mem_mul h1 h3) (mem_neg (mem_pow h2 2))
  have hu : sixUBox.Mem sixU := by
    apply mem_div _ hd
    simpa only [uNumeratorBox,uNumerator,sub_eq_add_neg] using
      mem_add (mem_mul h2 h3) (mem_neg (mem_mul h1 h4))
  have hv : sixVBox.Mem sixV := by
    apply mem_div _ hd
    simpa only [vNumeratorBox,vNumerator,sub_eq_add_neg] using
      mem_add (mem_mul h2 h4) (mem_neg (mem_pow h3 2))
  have hh := mem_add (mem_add (mem_add (mem_add
    (mem_mul (mem_mul (mem_point (-10)) (mem_pow hv 2)) h2)
    (mem_mul (mem_mul (mem_mul (mem_point (-168)) hu) hv) h3))
    (mem_mul (mem_mul (mem_point (-60))
      (mem_add (mem_pow hu 2) (mem_mul (mem_point 14) hv))) h4))
    (mem_mul (mem_mul (mem_point (-484)) hu) h5)) (mem_mul (mem_point (-182)) h6)
  refine ⟨hd,hu,hv,?_⟩
  dsimp only [sixCorrectionBox]
  convert hh using 1
  norm_num only [Int.cast_neg,Int.cast_ofNat]
  unfold sixCorrection
  ring

theorem prefix_delta_positive : 0<prefixDelta :=
  pos_of_mem source_box_membership.1 delta_box_positive

/-- The two old-block equations are solved algebraically, using only the
certified nonzero determinant. No positivity of the new residual is used. -/
theorem six_critical_old_rows :
    canonicalCompletedNativeLogDerivativeMoment 1*sixV+
      canonicalCompletedNativeLogDerivativeMoment 2*sixU+canonicalCompletedNativeLogDerivativeMoment 3=0 ∧
    canonicalCompletedNativeLogDerivativeMoment 2*sixV+
      canonicalCompletedNativeLogDerivativeMoment 3*sixU+canonicalCompletedNativeLogDerivativeMoment 4=0 := by
  have hn := prefix_delta_positive.ne'
  unfold sixU sixV uNumerator vNumerator
  constructor <;> field_simp [hn] <;> unfold prefixDelta <;> ring


theorem six_critical_limit_residual : sixLimit sixU sixV=
    2*(canonicalCompletedNativeLogDerivativeMoment 5+
      sixU*canonicalCompletedNativeLogDerivativeMoment 4+
      sixV*canonicalCompletedNativeLogDerivativeMoment 3) := by
  obtain ⟨h1,h2⟩ := six_critical_old_rows
  unfold sixLimit
  linear_combination 2*sixU*h2+2*sixV*h1

/-- Independent source inclusion fixes the correction sign, not the pivot. -/
theorem six_critical_correction_positive : 0<sixCorrection sixU sixV :=
  pos_of_mem source_box_membership.2.2.2 six_correction_box_positive

theorem six_energy_eventually_above :
    ∀ᶠ k : ℕ in atTop, sixLimit sixU sixV<(sixEnergy sixU sixV (canonicalGreenJetStep k)).re := by
  have hl := Complex.continuous_re.continuousAt.tendsto.comp (six_correction_tendsto sixU sixV)
  have hp : ∀ᶠ k : ℕ in atTop, 0<((sixEnergy sixU sixV (canonicalGreenJetStep k)-
      (sixLimit sixU sixV:ℂ))/canonicalGreenJetStep k^2).re :=
    Filter.Tendsto.eventually_lt tendsto_const_nhds hl six_critical_correction_positive
  filter_upwards [hp] with k hk
  have hr : canonicalGreenJetStep k=(((((k:ℝ)+1)⁻¹):ℝ):ℂ) := by
    unfold canonicalGreenJetStep
    push_cast
    rfl
  rw [hr,← Complex.ofReal_pow,Complex.div_ofReal_re,Complex.sub_re,Complex.ofReal_re] at hk
  have hs : 0<(((k:ℝ)+1)⁻¹)^2 := by positivity
  have hh := mul_pos hk hs
  rw [div_mul_cancel₀ _ (ne_of_gt hs)] at hh
  simpa only [hr] using (sub_pos.mp hh)

end
end CarryMaterialVariation
