import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace CarryMeanContrast
open MeasureTheory Set intervalIntegral
noncomputable section
set_option autoImplicit false

def greenDensity (η x : ℝ) : ℝ := x^2*η*(2-η*x)/(1-η*x)^2
def greenBudget (η : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, greenDensity η x

theorem green_density_remainder (η x : ℝ) (h : 1-η*x≠0) :
    greenDensity η x-(2*η*x^2+3*η^2*x^3)=
      x^2*η*(η*x)^2*(4-3*η*x)/(1-η*x)^2 := by
  unfold greenDensity
  have hp : x^2*η*(2-η*x)=(2*η*x^2+3*η^2*x^3)*(1-η*x)^2+
      x^2*η*(η*x)^2*(4-3*η*x) := by ring
  rw [hp,add_div,mul_div_cancel_right₀ _ (pow_ne_zero 2 h)]
  ring

theorem green_density_lower (η : ℝ) (hη0 : 0≤η) (hη1 : η<1)
    (x : ℝ) (hx : x∈Icc (0 : ℝ) 1) :
    2*η*x^2+3*η^2*x^3≤greenDensity η x := by
  have ht0 : 0≤η*x := mul_nonneg hη0 hx.1
  have ht1 : η*x<1 := lt_of_le_of_lt (mul_le_of_le_one_right hη0 hx.2) hη1
  have hden : 1-η*x≠0 := ne_of_gt (by linarith)
  have hr := green_density_remainder η x hden
  have h4 : 0≤4-3*η*x := by nlinarith
  have hnum : 0≤x^2*η*(η*x)^2*(4-3*η*x)/(1-η*x)^2 := by positivity
  linarith

theorem green_density_continuousOn (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) :
    ContinuousOn (greenDensity η) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  have h : η*x<1 := lt_of_le_of_lt (mul_le_of_le_one_right hη0 hx.2) hη1
  exact pow_ne_zero 2 (by linarith)

theorem green_budget_lower (η : ℝ) (hη0 : 0≤η) (hη1 : η<1) :
    2*η/3+3*η^2/4≤greenBudget η := by
  have hd : IntervalIntegrable (greenDensity η) volume (0 : ℝ) 1 :=
    (green_density_continuousOn η hη0 hη1).intervalIntegrable_of_Icc (by norm_num)
  have hp : IntervalIntegrable (fun x : ℝ => 2*η*x^2+3*η^2*x^3) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => 2*η*x^2+3*η^2*x^3)).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ)≤1) hp hd
    (green_density_lower η hη0 hη1)
  have he : (∫ x in (0 : ℝ)..1, (2*η*x^2+3*η^2*x^3))=2*η/3+3*η^2/4 := by
    rw [intervalIntegral.integral_add]
    · simp only [intervalIntegral.integral_const_mul,integral_pow]
      norm_num
      ring
    · exact (by fun_prop : Continuous (fun x : ℝ => 2*η*x^2)).intervalIntegrable 0 1
    · exact (by fun_prop : Continuous (fun x : ℝ => 3*η^2*x^3)).intervalIntegrable 0 1
  rw [he] at h
  exact h

theorem c2_green_budget_gt_half : (1 : ℝ)/2<greenBudget (1/Real.sqrt 2) := by
  have hs0 : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1<Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs2 : Real.sqrt 2<2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hsq : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hη0 : 0≤1/Real.sqrt 2 := by positivity
  have hη1 : 1/Real.sqrt 2<1 := (div_lt_one hs0).mpr hs1
  have h := green_budget_lower (1/Real.sqrt 2) hη0 hη1
  have hbase : (1 : ℝ)/2<2*(1/Real.sqrt 2)/3+3*(1/Real.sqrt 2)^2/4 := by
    field_simp
    nlinarith
  exact lt_of_lt_of_le hbase h

end
end CarryMeanContrast
