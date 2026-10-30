import SigmaCenterAll

namespace CarrySigmaSource
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000

/-- Off-center coefficients of the pre-existing completed Green response.
Equality with the log-modulus jets off center is a separate obligation. -/
def sigmaGreenMoment (d : ℝ) (n : ℕ) : ℝ :=
  (((2*n+1).factorial:ℝ)⁻¹) *
    (iteratedDeriv (2*n+1) centerGreenResponse (-(Complex.I)*(d:ℂ))).re

theorem sigma_green_center_eq_canonical (n : ℕ) :
    sigmaGreenMoment 0 n = canonicalCompletedNativeLogDerivativeMoment n := by
  have hc := completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical n
  change (iteratedDeriv (2*n+1) centerGreenResponse 0 /
    ((2*n+1).factorial:ℂ)) = (canonicalCompletedNativeLogDerivativeMoment n:ℂ) at hc
  have hcast : (((2*n+1).factorial:ℝ):ℂ) = ((2*n+1).factorial:ℂ) := by norm_cast
  rw [← hcast] at hc
  have hcR := congrArg Complex.re hc
  simp only [Complex.div_ofReal_re,Complex.ofReal_re] at hcR
  unfold sigmaGreenMoment
  simpa [div_eq_mul_inv,mul_comm] using hcR

/-- A complex analytic function read along the true sigma-displacement. -/
theorem sigma_path_real_hasDerivAt (F : ℂ → ℂ) (d : ℝ)
    (hF : AnalyticAt ℂ F (-(Complex.I)*(d:ℂ))) :
    HasDerivAt (fun x : ℝ => (F (-(Complex.I)*(x:ℂ))).re)
      ((-(Complex.I))*deriv F (-(Complex.I)*(d:ℂ))).re d := by
  have hp : HasDerivAt (fun z : ℂ => -(Complex.I)*z) (-(Complex.I)) (d:ℂ) := by
    simpa using (hasDerivAt_id (d:ℂ)).const_mul (-(Complex.I))
  have hf : HasDerivAt F (deriv F (-(Complex.I)*(d:ℂ))) (-(Complex.I)*(d:ℂ)) :=
    hF.differentiableAt.hasDerivAt
  have hc := hf.comp (d:ℂ) hp
  simpa only [Function.comp_def,mul_comm] using hc.real_of_complex

/-- The raw second displacement derivative of each completed Green jet. -/
theorem sigma_green_raw_second_deriv (m : ℕ) :
    iteratedDeriv 2 (fun d : ℝ => (iteratedDeriv m centerGreenResponse (-(Complex.I)*(d:ℂ))).re) 0 =
      -(iteratedDeriv (m+2) centerGreenResponse 0).re := by
  have h0 : AnalyticAt ℂ centerGreenResponse 0 := completedNativeGreenNormalizedResponse_analyticAt
  have han (z : ℂ) (hz : AnalyticAt ℂ centerGreenResponse z) (n : ℕ) :
      AnalyticAt ℂ (iteratedDeriv n centerGreenResponse) z := by
    rw [iteratedDeriv_eq_iterate]
    exact hz.iterated_deriv n
  have hnear : ∀ᶠ d : ℝ in 𝓝 (0:ℝ), AnalyticAt ℂ centerGreenResponse (-(Complex.I)*(d:ℂ)) := by
    have hp : ContinuousAt (fun d : ℝ => -(Complex.I)*(d:ℂ)) 0 := by fun_prop
    have ht : ∀ᶠ z : ℂ in 𝓝 (-(Complex.I)*(0:ℂ)), AnalyticAt ℂ centerGreenResponse z := by
      simpa using h0.eventually_analyticAt
    exact hp.tendsto ht
  have he : deriv (fun d : ℝ => (iteratedDeriv m centerGreenResponse (-(Complex.I)*(d:ℂ))).re) =ᶠ[𝓝 (0:ℝ)]
      fun d : ℝ => (-(Complex.I)*iteratedDeriv (m+1) centerGreenResponse (-(Complex.I)*(d:ℂ))).re := by
    filter_upwards [hnear] with d hd
    have hd' := sigma_path_real_hasDerivAt (iteratedDeriv m centerGreenResponse) d (han _ hd m)
    simpa [iteratedDeriv_succ] using hd'.deriv
  have ha : AnalyticAt ℂ (fun z => -(Complex.I)*iteratedDeriv (m+1) centerGreenResponse z) 0 :=
    analyticAt_const.mul (han 0 h0 (m+1))
  have hh := sigma_path_real_hasDerivAt
    (fun z => -(Complex.I)*iteratedDeriv (m+1) centerGreenResponse z) 0 (by simpa using ha)
  have heval : deriv (fun z : ℂ => -(Complex.I)*iteratedDeriv (m+1) centerGreenResponse z) 0 =
      -(Complex.I)*iteratedDeriv (m+2) centerGreenResponse 0 := by
    have hm : deriv (iteratedDeriv (m+1) centerGreenResponse) =
        iteratedDeriv (m+2) centerGreenResponse := by
      simpa only [show m+2=(m+1)+1 by omega] using
        (iteratedDeriv_succ (n:=m+1) (f:=centerGreenResponse)).symm
    rw [← hm]
    exact ((han 0 h0 (m+1)).differentiableAt.hasDerivAt.const_mul (-(Complex.I))).deriv
  rw [show (2:ℕ)=1+1 by omega,iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq]
  have hd := hh.deriv
  simp only [Complex.ofReal_zero,mul_zero,heval] at hd
  have hh' : -(Complex.I)*(-(Complex.I)*iteratedDeriv (m+2) centerGreenResponse 0) =
      -iteratedDeriv (m+2) centerGreenResponse 0 := by
    have hi : Complex.I*Complex.I = -1 := Complex.I_mul_I
    calc
      _ = (Complex.I*Complex.I)*iteratedDeriv (m+2) centerGreenResponse 0 := by ring
      _ = _ := by rw [hi]; ring
  rw [hh'] at hd
  simpa only [Complex.neg_re] using hd

theorem sigma_green_curvature_at_center (n : ℕ) :
    iteratedDeriv 2 (fun d : ℝ => sigmaGreenMoment d n) 0 =
      -2*((n:ℝ)+1)*(2*(n:ℝ)+3)*canonicalCompletedNativeLogDerivativeMoment (n+1) := by
  unfold sigmaGreenMoment
  rw [iteratedDeriv_const_mul_field,sigma_green_raw_second_deriv]
  have hc := completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical (n+1)
  have hindex : 2*(n+1)+1=(2*n+1)+2 := by omega
  rw [hindex] at hc
  change (iteratedDeriv ((2*n+1)+2) centerGreenResponse 0 /
    (((2*n+1)+2).factorial:ℂ)) = (canonicalCompletedNativeLogDerivativeMoment (n+1):ℂ) at hc
  have hcast : (((((2*n+1)+2).factorial:ℝ)):ℂ) = ((((2*n+1)+2).factorial):ℂ) := by norm_cast
  rw [← hcast] at hc
  have hcR := congrArg Complex.re hc
  simp only [Complex.div_ofReal_re,Complex.ofReal_re] at hcR
  have hfac : ((((2*n+1)+2).factorial):ℝ) ≠ 0 := by positivity
  have hre : (iteratedDeriv ((2*n+1)+2) centerGreenResponse 0).re =
      canonicalCompletedNativeLogDerivativeMoment (n+1)*((((2*n+1)+2).factorial):ℝ) :=
    (div_eq_iff hfac).mp hcR
  rw [hre]
  have hf : (((2*n+1)+2).factorial:ℝ) =
      ((2*n+3:ℕ):ℝ)*((2*n+2:ℕ):ℝ)*((2*n+1).factorial:ℝ) := by
    rw [show (2*n+1)+2=((2*n+1)+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  push_cast
  field_simp

end
end CarrySigmaSource
