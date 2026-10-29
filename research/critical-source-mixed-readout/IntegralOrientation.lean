import SourceCoordinates
import PivotFromIntegral
import SourceIntegral

/-! New finite source inequalities from the EXISTING theta integral boxes.
No decimal checkpoint, Hankel positivity premise or spectral input. -/
namespace CarryCriticalMixed
open CarrySelfAdjointOperator CarryIntegralCertificate CarryCriticalSource
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

def nonlinearMarginBox : Box :=
  ((logMomentBox 0).mul (logMomentBox 2)).add
    (((Box.point 2).mul ((logMomentBox 1).pow 2)).neg)

def correctionSignBox : Box :=
  (((Box.point 2).mul ((logMomentBox 1).pow 3)).add
    ((((Box.point (-80)).mul (logMomentBox 0)).mul (logMomentBox 1)).mul (logMomentBox 2))).add
      (((Box.point 28).mul ((logMomentBox 0).pow 2)).mul (logMomentBox 3))

theorem nonlinearMarginBox_positive : nonlinearMarginBox.positive = true := by decide +kernel

theorem correctionSignBox_positive : correctionSignBox.positive = true := by decide +kernel

theorem source_nonlinear_margin_pos : 0 < h 0*h 2 - 2*(h 1)^2 := by
  have h0 := mem_logMomentBox material_theta_integral_input 0
  have h1 := mem_logMomentBox material_theta_integral_input 1
  have h2 := mem_logMomentBox material_theta_integral_input 2
  have hb := mem_add (mem_mul h0 h2) (mem_neg (mem_mul (mem_point 2) (mem_pow h1 2)))
  apply pos_of_mem (i := nonlinearMarginBox) _ nonlinearMarginBox_positive
  simpa only [nonlinearMarginBox, Int.cast_ofNat, sub_eq_add_neg] using hb

theorem source_correction_numerator_pos :
    0 < 2*(h 1)^3-80*h 0*h 1*h 2+28*(h 0)^2*h 3 := by
  have h0 := mem_logMomentBox material_theta_integral_input 0
  have h1 := mem_logMomentBox material_theta_integral_input 1
  have h2 := mem_logMomentBox material_theta_integral_input 2
  have h3 := mem_logMomentBox material_theta_integral_input 3
  have hb := mem_add
    (mem_add (mem_mul (mem_point 2) (mem_pow h1 3))
      (mem_mul (mem_mul (mem_mul (mem_point (-80)) h0) h1) h2))
    (mem_mul (mem_mul (mem_point 28) (mem_pow h0 2)) h3)
  apply pos_of_mem (i := correctionSignBox) _ correctionSignBox_positive
  dsimp only [correctionSignBox]
  convert hb using 1
  push_cast
  ring

end
end CarryCriticalMixed
