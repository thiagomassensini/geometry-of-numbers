import AnalyticExtraction
import KernelCoefficient

/-! Analytic numerator of the ORIGINAL completed dslope sampled on the two
conjugate shifted rays. Its finite sum is formed after the existing complete
source/kernel identification; it is not a new source or positive kernel. -/
namespace CarryAllOrderCorrection
open CarrySelfAdjointOperator CarrySourceLaw Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

abbrev response := completedGreenNormalizedResponse
  completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion

def rawAtom (r s : ℕ) (t : ℂ) : ℂ :=
  response ((Complex.I*(s+1:ℂ))*t) - response ((-Complex.I*(r+1:ℂ))*t)

def rawGreenRay (p q : ℕ) (t : ℂ) : ℂ :=
  ∑ r ∈ Finset.range (p+1), ∑ s ∈ Finset.range (q+1),
    completedGreenForwardWeight p r * completedGreenForwardWeight q s /
      (Complex.I*(r+s+2:ℂ)) * rawAtom r s t

theorem response_ray_analytic (c : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => response (c*t)) 0 :=
  completedNativeGreenNormalizedResponse_analyticAt.fun_comp_of_eq
    (by fun_prop) (by simp)

theorem rawAtom_analytic (r s : ℕ) : AnalyticAt ℂ (rawAtom r s) 0 :=
  (response_ray_analytic _).sub (response_ray_analytic _)

theorem rawGreenRay_analytic (p q : ℕ) : AnalyticAt ℂ (rawGreenRay p q) 0 := by
  unfold rawGreenRay
  apply Finset.analyticAt_fun_sum
  intro r _
  apply Finset.analyticAt_fun_sum
  intro s _
  exact analyticAt_const.mul (rawAtom_analytic r s)

theorem rawAtom_coefficient (r s d : ℕ) :
    taylorCoefficient (rawAtom r s) d =
      ((Complex.I*(s+1:ℂ))^d-(-Complex.I*(r+1:ℂ))^d)*
        completedNativeGreenResponseTaylorCoefficient d := by
  unfold taylorCoefficient rawAtom completedNativeGreenResponseTaylorCoefficient
  rw [iteratedDeriv_fun_sub (response_ray_analytic _).contDiffAt
      (response_ray_analytic _).contDiffAt,
    iteratedDeriv_comp_mul_zero, iteratedDeriv_comp_mul_zero]
  ring

theorem rawGreenRay_coefficient (p q d : ℕ) :
    taylorCoefficient (rawGreenRay p q) d =
      ∑ r ∈ Finset.range (p+1), ∑ s ∈ Finset.range (q+1),
        completedGreenForwardWeight p r*completedGreenForwardWeight q s /
          (Complex.I*(r+s+2:ℂ))*taylorCoefficient (rawAtom r s) d := by
  unfold taylorCoefficient rawGreenRay
  rw [iteratedDeriv_fun_sum]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    rw [iteratedDeriv_fun_sum]
    · rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      rw [iteratedDeriv_const_mul_field]
      ring
    · intro s _
      exact (analyticAt_const.mul (rawAtom_analytic r s)).contDiffAt
  · intro r _
    exact (Finset.analyticAt_fun_sum _ (fun s _ =>
      analyticAt_const.mul (rawAtom_analytic r s))).contDiffAt

theorem rawGreenRay_even (p q j : ℕ) :
    taylorCoefficient (rawGreenRay p q) (2*j) = 0 := by
  rw [rawGreenRay_coefficient]
  simp only [rawAtom_coefficient, completedNativeGreenResponseTaylorCoefficient_even_eq_zero,
    mul_zero, Finset.sum_const_zero]

/-- Exact odd coefficient of the complete shifted Cauchy cross. -/
theorem rawAtom_odd_quotient (r s j : ℕ) :
    taylorCoefficient (rawAtom r s) (2*j+1) / (Complex.I*(r+s+2:ℂ)) =
      (-1:ℂ)^j * (canonicalCompletedNativeLogDerivativeMoment j:ℂ) *
        ((((r+1:ℝ)^(2*j+1)+(s+1:ℝ)^(2*j+1))/(r+s+2:ℝ)):ℂ) := by
  rw [rawAtom_coefficient, completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  have hp : Complex.I^(2*j+1) = (-1:ℂ)^j*Complex.I := by
    rw [pow_add,pow_mul,Complex.I_sq,pow_one]
  have hn : (-Complex.I)^(2*j+1) = -((-1:ℂ)^j*Complex.I) := by
    rw [neg_pow,Odd.neg_one_pow (show Odd (2*j+1) from ⟨j,by omega⟩),hp]
    ring
  rw [mul_pow,mul_pow,hp,hn]
  have hd : (r+s+2:ℂ) ≠ 0 := by
    exact_mod_cast (show (r+s+2:ℝ) ≠ 0 by positivity)
  push_cast
  field_simp
  ring

theorem forwardWeight_eq_real (p r : ℕ) :
    completedGreenForwardWeight p r = ((completedGreenForwardWeight p r).re:ℂ) := by
  apply Complex.ext
  · simp
  · simp only [completedGreenForwardWeight, Complex.intCast_im, Complex.ofReal_im]

/-- The arbitrary-order contractions of PR #44 are now the actual Taylor
coefficients of the analytic original-source numerator. -/
theorem rawGreenRay_odd (p q j : ℕ) :
    taylorCoefficient (rawGreenRay p q) (2*j+1) =
      (-1:ℂ)^j*(canonicalCompletedNativeLogDerivativeMoment j:ℂ)*
        (greenContraction p q (2*j):ℂ) := by
  rw [rawGreenRay_coefficient, ← source_power_coefficient_exact p q j]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  calc
    _ = completedGreenForwardWeight p r*completedGreenForwardWeight q s *
        (taylorCoefficient (rawAtom r s) (2*j+1)/(Complex.I*(r+s+2:ℂ))) := by ring
    _ = _ := by
      rw [rawAtom_odd_quotient,forwardWeight_eq_real p r,forwardWeight_eq_real q s]
      simp only [Complex.ofReal_re]
      push_cast
      ring

end
end CarryAllOrderCorrection
