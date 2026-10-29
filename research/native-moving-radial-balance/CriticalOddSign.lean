import CriticalOddTaylor
import IntegralCertificate

namespace CarryMovingRadial
open CarrySelfAdjointOperator CarryIntegralCertificate Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

def orientationPolynomial (u v w z : ℝ) : ℝ := -10*v^3+168*u*v*w-60*u^2*z
def orientationBox : Box :=
  ((((Box.point 10).mul ((logMomentBox 2).pow 3)).neg).add
    ((((Box.point 168).mul (logMomentBox 1)).mul (logMomentBox 2)).mul (logMomentBox 3))).add
      ((((Box.point 60).mul ((logMomentBox 1).pow 2)).mul (logMomentBox 4)).neg)

theorem orientation_box_positive : orientationBox.positive=true := by decide +kernel
theorem h1_box_positive : (logMomentBox 1).positive=true := by decide +kernel

/-- Source-derived orientation, independent of canonical pivot positivity. -/
theorem source_orientation_positive : orientationPolynomial
    (canonicalCompletedNativeLogDerivativeMoment 1)
    (canonicalCompletedNativeLogDerivativeMoment 2)
    (canonicalCompletedNativeLogDerivativeMoment 3)
    (canonicalCompletedNativeLogDerivativeMoment 4)>0 := by
  have h1 := mem_logMomentBox material_theta_integral_input 1
  have h2 := mem_logMomentBox material_theta_integral_input 2
  have h3 := mem_logMomentBox material_theta_integral_input 3
  have h4 := mem_logMomentBox material_theta_integral_input 4
  have hh := mem_add (mem_add (mem_neg (mem_mul (mem_point 10) (mem_pow h2 3)))
    (mem_mul (mem_mul (mem_mul (mem_point 168) h1) h2) h3))
    (mem_neg (mem_mul (mem_mul (mem_point 60) (mem_pow h1 2)) h4))
  have hm : orientationBox.Mem (orientationPolynomial
      (canonicalCompletedNativeLogDerivativeMoment 1)
      (canonicalCompletedNativeLogDerivativeMoment 2)
      (canonicalCompletedNativeLogDerivativeMoment 3)
      (canonicalCompletedNativeLogDerivativeMoment 4)) := by
    unfold orientationBox
    convert hh using 1
    norm_num only [Int.cast_ofNat]
    unfold orientationPolynomial
    ring
  exact pos_of_mem hm orientation_box_positive

def criticalParameter : ℝ := canonicalCompletedNativeLogDerivativeMoment 2/
  canonicalCompletedNativeLogDerivativeMoment 1

theorem critical_correction_positive : 0<criticalCorrection criticalParameter := by
  have hp := pos_of_mem (mem_logMomentBox material_theta_integral_input 1) h1_box_positive
  have hn := hp.ne'
  have he : criticalCorrection criticalParameter*(canonicalCompletedNativeLogDerivativeMoment 1)^2=
      orientationPolynomial (canonicalCompletedNativeLogDerivativeMoment 1)
        (canonicalCompletedNativeLogDerivativeMoment 2)
        (canonicalCompletedNativeLogDerivativeMoment 3)
        (canonicalCompletedNativeLogDerivativeMoment 4) := by
    unfold criticalCorrection criticalParameter orientationPolynomial
    field_simp [hn]
  have hs : 0<(canonicalCompletedNativeLogDerivativeMoment 1)^2 := sq_pos_of_ne_zero hn
  exact (mul_pos_iff_of_pos_right hs).mp (he.symm ▸ source_orientation_positive)

theorem critical_energy_eventually_above :
    ∀ᶠ k : ℕ in atTop, criticalLimit criticalParameter<
      (criticalEnergy criticalParameter (canonicalGreenJetStep k)).re := by
  have hl := Complex.continuous_re.continuousAt.tendsto.comp
    (critical_correction_tendsto criticalParameter)
  have hp : ∀ᶠ k : ℕ in atTop, 0<
      ((criticalEnergy criticalParameter (canonicalGreenJetStep k)-
        (criticalLimit criticalParameter:ℂ))/canonicalGreenJetStep k^2).re :=
    Filter.Tendsto.eventually_lt tendsto_const_nhds hl critical_correction_positive
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
end CarryMovingRadial
