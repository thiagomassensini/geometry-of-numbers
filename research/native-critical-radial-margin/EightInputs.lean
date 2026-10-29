import SixBoundary
import IntegralCertificate

namespace CarryCriticalRadialMargin
open CarrySelfAdjointOperator CarryIntegralCertificate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem

/-- Outer rational enclosures for the unmodified canonical source moments.
These are certified against the pre-existing complete theta integrals. -/
def momentBox1 : Box := .finite 37172599285269644000000000000000000000000000000000000000 37172599285269709000000000000000000000000000000000000000
def momentBox2 : Box := .finite 144173931400969200000000000000000000000000000000000000 144173931400979100000000000000000000000000000000000000
def momentBox3 : Box := .finite 663031680252680000000000000000000000000000000000000 663031680253330000000000000000000000000000000000000
def momentBox4 : Box := .finite 3213664150602000000000000000000000000000000000000 3213664150630000000000000000000000000000000000000
def momentBox5 : Box := .finite 15876934514400000000000000000000000000000000000 15876934515400000000000000000000000000000000000
def momentBox6 : Box := .finite 79033257220000000000000000000000000000000000 79033257260000000000000000000000000000000000
def momentBox7 : Box := .finite 394647139500000000000000000000000000000000 394647140600000000000000000000000000000000

theorem moment_box_1_mem : momentBox1.Mem (canonicalCompletedNativeLogDerivativeMoment 1) := by
  apply mem_of_contained (mem_logMomentBox material_theta_integral_input 1)
  exact (show (logMomentBox 1).contained momentBox1 = true by decide +kernel)

theorem moment_box_2_mem : momentBox2.Mem (canonicalCompletedNativeLogDerivativeMoment 2) := by
  apply mem_of_contained (mem_logMomentBox material_theta_integral_input 2)
  exact (show (logMomentBox 2).contained momentBox2 = true by decide +kernel)

theorem moment_box_3_mem : momentBox3.Mem (canonicalCompletedNativeLogDerivativeMoment 3) := by
  apply mem_of_contained (mem_logMomentBox material_theta_integral_input 3)
  exact (show (logMomentBox 3).contained momentBox3 = true by decide +kernel)

theorem moment_box_4_mem : momentBox4.Mem (canonicalCompletedNativeLogDerivativeMoment 4) := by
  apply mem_of_contained (mem_logMomentBox material_theta_integral_input 4)
  exact (show (logMomentBox 4).contained momentBox4 = true by decide +kernel)

theorem moment_box_5_mem : momentBox5.Mem (canonicalCompletedNativeLogDerivativeMoment 5) := by
  apply mem_of_contained (mem_logMomentBox material_theta_integral_input 5)
  exact (show (logMomentBox 5).contained momentBox5 = true by decide +kernel)

theorem moment_box_6_mem : momentBox6.Mem (canonicalCompletedNativeLogDerivativeMoment 6) := by
  apply mem_of_contained (mem_logMomentBox material_theta_integral_input 6)
  exact (show (logMomentBox 6).contained momentBox6 = true by decide +kernel)

theorem moment_box_7_mem : momentBox7.Mem (canonicalCompletedNativeLogDerivativeMoment 7) := by
  apply mem_of_contained (mem_logMomentBox material_theta_integral_input 7)
  exact (show (logMomentBox 7).contained momentBox7 = true by decide +kernel)

end
end CarryCriticalRadialMargin
