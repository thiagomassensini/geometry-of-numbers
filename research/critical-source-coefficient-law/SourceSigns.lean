import IntegralOrientation

/-! Exact rational interval tests on the existing ORIGINAL theta integrals.
These new source inequalities do not import a later Hankel positivity proof. -/
namespace CarrySourceLaw
open CarrySelfAdjointOperator CarryIntegralCertificate CarryCriticalSource
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

def oddCorrectionBox : Box :=
  (((Box.point (-10)).mul ((logMomentBox 2).pow 3)).add
    ((((Box.point 168).mul (logMomentBox 1)).mul (logMomentBox 2)).mul (logMomentBox 3))).add
      (((Box.point (-60)).mul ((logMomentBox 1).pow 2)).mul (logMomentBox 4))

def oddPivotBox : Box :=
  ((logMomentBox 1).mul (logMomentBox 3)).add (((logMomentBox 2).pow 2).neg)

theorem oddCorrectionBox_positive : oddCorrectionBox.positive = true := by decide +kernel
theorem oddPivotBox_positive : oddPivotBox.positive = true := by decide +kernel

theorem source_h1_pos : 0 < h 1 := by
  apply pos_of_mem (mem_logMomentBox material_theta_integral_input 1)
  decide +kernel

theorem source_odd_correction_pos :
    0 < -10*(h 2)^3+168*h 1*h 2*h 3-60*(h 1)^2*h 4 := by
  have h1 := mem_logMomentBox material_theta_integral_input 1
  have h2 := mem_logMomentBox material_theta_integral_input 2
  have h3 := mem_logMomentBox material_theta_integral_input 3
  have h4 := mem_logMomentBox material_theta_integral_input 4
  have hb := mem_add
    (mem_add (mem_mul (mem_point (-10)) (mem_pow h2 3))
      (mem_mul (mem_mul (mem_mul (mem_point 168) h1) h2) h3))
    (mem_mul (mem_mul (mem_point (-60)) (mem_pow h1 2)) h4)
  apply pos_of_mem (i := oddCorrectionBox) _ oddCorrectionBox_positive
  dsimp only [oddCorrectionBox]
  convert hb using 1
  push_cast
  ring

theorem source_odd_pivot_margin_pos : 0 < h 1*h 3-(h 2)^2 := by
  have hb := mem_add
    (mem_mul (mem_logMomentBox material_theta_integral_input 1)
      (mem_logMomentBox material_theta_integral_input 3))
    (mem_neg (mem_pow (mem_logMomentBox material_theta_integral_input 2) 2))
  apply pos_of_mem (i := oddPivotBox) _ oddPivotBox_positive
  simpa only [oddPivotBox, sub_eq_add_neg] using hb

end
end CarrySourceLaw
