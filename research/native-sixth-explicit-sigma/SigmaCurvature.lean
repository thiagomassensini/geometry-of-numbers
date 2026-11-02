import SigmaOffcenterBridge

namespace CarrySigmaSource
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 16000000

theorem sigma_green_raw_second_deriv_at (m : ℕ) (d : ℝ)
    (h0 : AnalyticAt ℂ centerGreenResponse (-(Complex.I)*(d:ℂ))) :
    iteratedDeriv 2 (fun x : ℝ => (iteratedDeriv m centerGreenResponse (-(Complex.I)*(x:ℂ))).re) d =
      -(iteratedDeriv (m+2) centerGreenResponse (-(Complex.I)*(d:ℂ))).re := by
  have han (z : ℂ) (hz : AnalyticAt ℂ centerGreenResponse z) (n : ℕ) :
      AnalyticAt ℂ (iteratedDeriv n centerGreenResponse) z := by
    rw [iteratedDeriv_eq_iterate]
    exact hz.iterated_deriv n
  have hnear : ∀ᶠ x : ℝ in 𝓝 d, AnalyticAt ℂ centerGreenResponse (-(Complex.I)*(x:ℂ)) := by
    have hp : ContinuousAt (fun x : ℝ => -(Complex.I)*(x:ℂ)) d := by fun_prop
    exact hp.tendsto h0.eventually_analyticAt
  have he : deriv (fun x : ℝ => (iteratedDeriv m centerGreenResponse (-(Complex.I)*(x:ℂ))).re) =ᶠ[𝓝 d]
      fun x : ℝ => (-(Complex.I)*iteratedDeriv (m+1) centerGreenResponse (-(Complex.I)*(x:ℂ))).re := by
    filter_upwards [hnear] with x hx
    have hx' := sigma_path_real_hasDerivAt (iteratedDeriv m centerGreenResponse) x (han _ hx m)
    simpa [iteratedDeriv_succ] using hx'.deriv
  have ha : AnalyticAt ℂ (fun z => -(Complex.I)*iteratedDeriv (m+1) centerGreenResponse z)
      (-(Complex.I)*(d:ℂ)) := analyticAt_const.mul (han _ h0 (m+1))
  have hh := sigma_path_real_hasDerivAt
    (fun z => -(Complex.I)*iteratedDeriv (m+1) centerGreenResponse z) d ha
  have heval : deriv (fun z : ℂ => -(Complex.I)*iteratedDeriv (m+1) centerGreenResponse z)
      (-(Complex.I)*(d:ℂ)) = -(Complex.I)*iteratedDeriv (m+2) centerGreenResponse (-(Complex.I)*(d:ℂ)) := by
    have hm : deriv (iteratedDeriv (m+1) centerGreenResponse) = iteratedDeriv (m+2) centerGreenResponse := by
      simpa only [show m+2=(m+1)+1 by omega] using
        (iteratedDeriv_succ (n:=m+1) (f:=centerGreenResponse)).symm
    rw [← hm]
    exact ((han _ h0 (m+1)).differentiableAt.hasDerivAt.const_mul (-(Complex.I))).deriv
  rw [show (2:ℕ)=1+1 by omega,iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq]
  have hd := hh.deriv
  rw [heval] at hd
  have hh' : -(Complex.I)*(-(Complex.I)*iteratedDeriv (m+2) centerGreenResponse (-(Complex.I)*(d:ℂ))) =
      -iteratedDeriv (m+2) centerGreenResponse (-(Complex.I)*(d:ℂ)) := by
    have hi : Complex.I*Complex.I = -1 := Complex.I_mul_I
    calc
      _ = (Complex.I*Complex.I)*iteratedDeriv (m+2) centerGreenResponse (-(Complex.I)*(d:ℂ)) := by ring
      _ = _ := by rw [hi]; ring
  rw [hh'] at hd
  simpa only [Complex.neg_re] using hd

theorem sigma_green_curvature_at (d : ℝ) (n : ℕ)
    (h0 : AnalyticAt ℂ centerGreenResponse (-(Complex.I)*(d:ℂ))) :
    iteratedDeriv 2 (fun x : ℝ => sigmaGreenMoment x n) d =
      -2*((n:ℝ)+1)*(2*(n:ℝ)+3)*sigmaGreenMoment d (n+1) := by
  unfold sigmaGreenMoment
  rw [iteratedDeriv_const_mul_field,sigma_green_raw_second_deriv_at _ _ h0]
  have hindex : 2*(n+1)+1=(2*n+1)+2 := by omega
  rw [hindex]
  have hf : (((2*n+1)+2).factorial:ℝ) =
      ((2*n+3:ℕ):ℝ)*((2*n+2:ℕ):ℝ)*((2*n+1).factorial:ℝ) := by
    rw [show (2*n+1)+2=((2*n+1)+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  push_cast
  field_simp

theorem sigma_log_green_eventuallyEq_at (d : ℝ) (n : ℕ)
    (ha : AnalyticAt ℂ completedNativeOperatorCharacteristic (displacedHeight d 0))
    (hne : completedSigmaResponse d 0 ≠ 0) :
    (fun x : ℝ => completedSigmaLogJet x n) =ᶠ[𝓝 d] (fun x : ℝ => sigmaGreenMoment x n) := by
  have hnon : ∀ᶠ z : ℂ in 𝓝 (displacedHeight d 0), completedNativeOperatorCharacteristic z ≠ 0 :=
    ha.continuousAt.eventually_ne hne
  have hp : ContinuousAt (fun x : ℝ => displacedHeight x 0) d := by
    unfold displacedHeight
    fun_prop
  have hnear := hp.tendsto (ha.eventually_analyticAt.and hnon)
  filter_upwards [hnear] with x hx
  exact displaced_log_jet_eq_green x n hx.1 hx.2

/-- Source-derived local sigma curvature of the original log-modulus jets,
without assuming Hharm or positivity. -/
theorem sigma_log_jet_curvature_at (d : ℝ) (n : ℕ)
    (ha : AnalyticAt ℂ completedNativeOperatorCharacteristic (displacedHeight d 0))
    (hne : completedSigmaResponse d 0 ≠ 0) :
    iteratedDeriv 2 (fun x : ℝ => completedSigmaLogJet x n) d =
      -2*((n:ℝ)+1)*(2*(n:ℝ)+3)*completedSigmaLogJet d (n+1) := by
  have hr := displaced_green_response_analytic d ha hne
  have hr' : AnalyticAt ℂ centerGreenResponse (-(Complex.I)*(d:ℂ)) := by
    simpa [displacedHeight] using hr
  rw [Filter.EventuallyEq.iteratedDeriv_eq 2 (sigma_log_green_eventuallyEq_at d n ha hne)]
  rw [sigma_green_curvature_at d n hr']
  rw [displaced_log_jet_eq_green d (n+1) ha hne]

/-- Unconditional central specialization, with the ORIGINAL canonical
moment on the right. -/
theorem sigma_log_jet_curvature_center (n : ℕ) :
    iteratedDeriv 2 (fun x : ℝ => completedSigmaLogJet x n) 0 =
      -2*((n:ℝ)+1)*(2*(n:ℝ)+3)*canonicalCompletedNativeLogDerivativeMoment (n+1) := by
  have ha : AnalyticAt ℂ completedNativeOperatorCharacteristic (displacedHeight 0 0) := by
    simpa [displacedHeight] using completedNativeOperatorCharacteristic_analyticAt zero_mem_completedNativeHeightDomain
  have hn : completedSigmaResponse 0 0 ≠ 0 := by
    simpa [completedSigmaResponse,displacedHeight] using completedNativeOperatorCharacteristic_zero_ne_zero
  rw [sigma_log_jet_curvature_at 0 n ha hn,sigma_log_jet_center_eq_canonical]

end
end CarrySigmaSource
