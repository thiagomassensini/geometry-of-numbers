import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Elementary polynomial integrals; no Gamma evaluation or source change. -/
namespace CarryMellinDomain
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory

/-- The energy integral is evaluated by reflection and four powers. -/
theorem cubic_one_sub_integral (m : ℕ) :
    (∫ u in (0:ℝ)..1, u^3*(1-u)^m)=
      6/(((m:ℝ)+1)*((m:ℝ)+2)*((m:ℝ)+3)*((m:ℝ)+4)) := by
  have hr := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => (1-u)^3*u^m) (a:=0) (b:=1) 1
  simp only [sub_sub_cancel,sub_self,sub_zero] at hr
  rw [hr]
  have he : (fun u : ℝ => (1-u)^3*u^m)=
      fun u => u^m-3*u^(m+1)+3*u^(m+2)-u^(m+3) := by
    funext u
    simp only [pow_add]
    ring
  rw [he,intervalIntegral.integral_sub,intervalIntegral.integral_add,
    intervalIntegral.integral_sub,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  · norm_num [integral_pow]
    have h1 : (m:ℝ)+1≠0 := by positivity
    have h2 : (m:ℝ)+2≠0 := by positivity
    have h3 : (m:ℝ)+3≠0 := by positivity
    have h4 : (m:ℝ)+4≠0 := by positivity
    field_simp [h1,h2,h3,h4]
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The same elementary reflection computes the actual Mellin readout. -/
theorem one_sub_integral (n : ℕ) (a : ℝ) :
    (∫ u in (0:ℝ)..a, (1-u)^n)=(1-(1-a)^(n+1))/((n:ℝ)+1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u^n) 1,integral_pow]
  simp only [sub_zero,one_pow]

end
end CarryMellinDomain
