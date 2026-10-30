import SigmaCenterZero

namespace CarrySigmaSource
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

def centerGreenResponse : ℂ → ℂ := completedGreenNormalizedResponse
  completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion

/-- Real restrictions of every derivative of the actual analytic Green
response agree locally with the real part of its complex derivatives. -/
theorem center_response_real_iteratedDeriv_eventually (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => (centerGreenResponse (t:ℂ)).re) =ᶠ[𝓝 (0:ℝ)]
      fun t : ℝ => (iteratedDeriv n centerGreenResponse (t:ℂ)).re := by
  let U : Set ℂ := {z | AnalyticAt ℂ centerGreenResponse z}
  have hopen : IsOpen U := isOpen_analyticAt ℂ centerGreenResponse
  have hz : (0:ℂ) ∈ U := completedNativeGreenNormalizedResponse_analyticAt
  have hdiff : DifferentiableOn ℂ centerGreenResponse U := by
    intro z hz'
    exact hz'.differentiableAt.differentiableWithinAt
  have hall (m : ℕ) : DifferentiableOn ℂ (iteratedDeriv m centerGreenResponse) U := by
    induction m with
    | zero => simpa using hdiff
    | succ m ih =>
        rw [show m+1=Nat.succ m by omega,iteratedDeriv_succ]
        exact ih.deriv hopen
  have hrealU : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), (t:ℂ) ∈ U := by
    have hc : ContinuousAt (fun t : ℝ => (t:ℂ)) 0 := by fun_prop
    exact hc.tendsto (hopen.mem_nhds hz)
  induction n with
  | zero => simp
  | succ n ih =>
      have ih' := ih.deriv
      filter_upwards [ih',hrealU] with t ht hU
      simp only [iteratedDeriv_succ]
      rw [ht]
      have hlocal := (hall n).differentiableAt (hopen.mem_nhds hU)
      exact hlocal.hasDerivAt.real_of_complex.deriv

/-- The original real logarithmic readout equals minus twice the real
part of the completed Green response on a nonvanishing neighborhood. -/
theorem center_log_deriv_eventually :
    deriv (fun t : ℝ => Real.log (centerRealSource t)) =ᶠ[𝓝 (0:ℝ)]
      fun t : ℝ => -2*(centerGreenResponse (t:ℂ)).re := by
  have hne : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), centerRealSource t ≠ 0 :=
    (center_real_source_hasDerivAt 0).continuousAt.eventually_ne center_real_source_ne_zero
  filter_upwards [hne] with t ht
  rw [deriv.log (center_real_source_hasDerivAt t).differentiableAt ht,
    (center_real_source_hasDerivAt t).deriv]
  have hf : completedNativeOperatorCharacteristic (t:ℂ) = (centerRealSource t:ℂ) := by
    have hi := completedNativeOperatorCharacteristic_ofReal_im_eq_zero t
    apply Complex.ext
    · simp [centerRealSource]
    · change (completedNativeOperatorCharacteristic (t:ℂ)).im = 0
      exact hi
  unfold centerGreenResponse completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv,hf]
  have hd : (2:ℂ)*(centerRealSource t:ℂ) = ((2*centerRealSource t:ℝ):ℂ) := by push_cast; ring
  rw [hd]
  simp only [Complex.div_ofReal_re,Complex.neg_re]
  field_simp [ht]

/-- The log-modulus jet of the original completed characteristic at the
center is exactly the existing native canonical moment in EVERY order. -/
theorem sigma_log_jet_center_eq_canonical (n : ℕ) :
    completedSigmaLogJet 0 n = canonicalCompletedNativeLogDerivativeMoment n := by
  rw [sigma_log_jet_center_formula]
  change -((n+1:ℕ):ℝ)/(((2*n+2).factorial:ℝ)) *
    iteratedDeriv (2*n+2) (fun t : ℝ => Real.log (centerRealSource t)) 0 = _
  rw [show 2*n+2=(2*n+1)+1 by omega,iteratedDeriv_succ']
  rw [Filter.EventuallyEq.iteratedDeriv_eq (2*n+1) center_log_deriv_eventually]
  rw [iteratedDeriv_const_mul_field]
  have hreal : iteratedDeriv (2*n+1) (fun t : ℝ => (centerGreenResponse (t:ℂ)).re) 0 =
      (iteratedDeriv (2*n+1) centerGreenResponse 0).re :=
    (center_response_real_iteratedDeriv_eventually (2*n+1)).eq_of_nhds
  rw [hreal]
  have hc := completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical n
  change (iteratedDeriv (2*n+1) centerGreenResponse 0 /
    ((2*n+1).factorial:ℂ)) = (canonicalCompletedNativeLogDerivativeMoment n:ℂ) at hc
  have hcast : (((2*n+1).factorial:ℝ):ℂ) = ((2*n+1).factorial:ℂ) := by norm_cast
  rw [← hcast] at hc
  have hcR := congrArg Complex.re hc
  simp only [Complex.div_ofReal_re,Complex.ofReal_re] at hcR
  have hfac : ((2*n+1).factorial:ℝ) ≠ 0 := by positivity
  have hre : (iteratedDeriv (2*n+1) centerGreenResponse 0).re =
      canonicalCompletedNativeLogDerivativeMoment n * ((2*n+1).factorial:ℝ) :=
    (div_eq_iff hfac).mp hcR
  rw [hre]
  have hf : ((2*n+2).factorial:ℝ) = ((2*n+2:ℕ):ℝ)*((2*n+1).factorial:ℝ) := by
    rw [show 2*n+2=(2*n+1)+1 by omega,Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  push_cast
  field_simp

end
end CarrySigmaSource
