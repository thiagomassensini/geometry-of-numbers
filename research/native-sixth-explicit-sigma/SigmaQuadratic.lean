import SigmaCurvature
import SchurLogic
import CarrySelfAdjointOperator.NativeSourceAllOrderSchur
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace CarrySigmaSource
open CarrySelfAdjointOperator NativeMomentOrthogonalization
open Filter Topology
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000

theorem sigma_green_moment_analytic_center (n : ℕ) :
    AnalyticAt ℝ (fun d => sigmaGreenMoment d n) 0 := by
  have hR : AnalyticAt ℂ centerGreenResponse 0 := completedNativeGreenNormalizedResponse_analyticAt
  have hd : AnalyticAt ℂ (iteratedDeriv (2*n+1) centerGreenResponse) 0 := by
    rw [iteratedDeriv_eq_iterate]
    exact hR.iterated_deriv (2*n+1)
  have hp : AnalyticAt ℂ (fun z : ℂ => -(Complex.I)*z) 0 := by fun_prop
  have hc : AnalyticAt ℂ (fun z : ℂ => iteratedDeriv (2*n+1) centerGreenResponse (-(Complex.I)*z)) 0 := by
    have hd' : AnalyticAt ℂ (iteratedDeriv (2*n+1) centerGreenResponse) (-(Complex.I)*(0:ℂ)) := by
      simpa using hd
    exact AnalyticAt.comp (f:=fun z : ℂ => -(Complex.I)*z) hd' hp
  have hr := hc.re_ofReal
  exact analyticAt_const.mul hr

theorem sigma_log_jet_analytic_center (n : ℕ) :
    AnalyticAt ℝ (fun d => completedSigmaLogJet d n) 0 := by
  have ha : AnalyticAt ℂ completedNativeOperatorCharacteristic (displacedHeight 0 0) := by
    simpa [displacedHeight] using completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
  have hn : completedSigmaResponse 0 0 ≠ 0 := by
    simpa [completedSigmaResponse,displacedHeight] using completedNativeOperatorCharacteristic_zero_ne_zero
  exact (sigma_green_moment_analytic_center n).congr (sigma_log_green_eventuallyEq_at 0 n ha hn).symm

def sigmaMomentForm (d : ℝ) (s N : ℕ) (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, v i*v j*completedSigmaLogJet d (i.val+j.val+s)

theorem sigma_moment_form_center (s N : ℕ) (v : Fin N → ℝ) :
    sigmaMomentForm 0 s N v = sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment s N v := by
  unfold sigmaMomentForm sourceMomentQuadratic
  simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,sourceMomentMatrix,Finset.mul_sum,
    sigma_log_jet_center_eq_canonical]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact completed source curvature for every finite coefficient family,
including all ordered mixed pairs, with no positivity assumption. -/
theorem sigma_moment_form_curvature_center (s N : ℕ) (v : Fin N → ℝ) :
    iteratedDeriv 2 (fun d => sigmaMomentForm d s N v) 0 =
      -2 * ∑ i : Fin N, ∑ j : Fin N, v i*v j *
        (((i.val+j.val+s:ℕ):ℝ)+1)*(2*((i.val+j.val+s:ℕ):ℝ)+3)*
        canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+s+1) := by
  have ht (i j : Fin N) : ContDiffAt ℝ 2
      (fun d => v i*v j*completedSigmaLogJet d (i.val+j.val+s)) 0 :=
    (analyticAt_const.mul (sigma_log_jet_analytic_center (i.val+j.val+s))).contDiffAt
  have hrow (i : Fin N) : ContDiffAt ℝ 2
      (fun d => ∑ j : Fin N, v i*v j*completedSigmaLogJet d (i.val+j.val+s)) 0 := by
    apply ContDiffAt.sum
    intro j hj
    exact ht i j
  unfold sigmaMomentForm
  rw [iteratedDeriv_fun_sum (fun i _ => hrow i)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_fun_sum (fun j _ => ht i j),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_const_mul_field,sigma_log_jet_curvature_center]
  ring

/-- The full original source has a stationary central log jet in every order. -/
theorem sigma_log_jet_deriv_center (n : ℕ) :
    deriv (fun d => completedSigmaLogJet d n) 0 = 0 :=
  sigma_log_jet_deriv_zero n (sigma_log_jet_analytic_center n).differentiableAt

/-- The original unshifted critical direction, without a positivity assumption. -/
def canonicalCriticalVector (s n : ℕ) : Fin (n+1) → ℝ :=
  Fin.snoc (-((sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)⁻¹ *ᵥ
    sourceMomentCoupling canonicalCompletedNativeLogDerivativeMoment s n)) 1

/-- Curvature at the unaltered canonical Schur vector, held fixed at the center.
Equality with the derivative of the moving pivot is not asserted. -/
theorem sigma_critical_form_curvature_center (s n : ℕ) :
    iteratedDeriv 2 (fun d => sigmaMomentForm d s (n+1) (canonicalCriticalVector s n)) 0 =
      -2 * ∑ i : Fin (n+1), ∑ j : Fin (n+1),
        canonicalCriticalVector s n i * canonicalCriticalVector s n j *
        (((i.val+j.val+s:ℕ):ℝ)+1)*(2*((i.val+j.val+s:ℕ):ℝ)+3)*
        canonicalCompletedNativeLogDerivativeMoment (i.val+j.val+s+1) :=
  sigma_moment_form_curvature_center s (n+1) (canonicalCriticalVector s n)

theorem sigma_critical_form_center_eq_schur (s n : ℕ)
    (hA : IsUnit (sourceMomentMatrix canonicalCompletedNativeLogDerivativeMoment s n)) :
    sigmaMomentForm 0 s (n+1) (canonicalCriticalVector s n) =
      sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment s n := by
  rw [sigma_moment_form_center]
  exact sourceMomentSchur_critical_direction_of_isUnit _ s n hA

end
end CarrySigmaSource
