import SigmaOffcenter

namespace CarrySigmaSource
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000000

theorem analytic_real_iteratedDeriv_at_zero (F : ℂ → ℂ) (h0 : AnalyticAt ℂ F 0) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => (F (t:ℂ)).re) 0 = (iteratedDeriv n F 0).re := by
  let U : Set ℂ := {z | AnalyticAt ℂ F z}
  have hopen : IsOpen U := isOpen_analyticAt ℂ F
  have hz : (0:ℂ) ∈ U := h0
  have hdiff : DifferentiableOn ℂ F U := by
    intro z hz'
    exact hz'.differentiableAt.differentiableWithinAt
  have hall (m : ℕ) : DifferentiableOn ℂ (iteratedDeriv m F) U := by
    induction m with
    | zero => simpa using hdiff
    | succ m ih =>
        rw [show m+1=Nat.succ m by omega,iteratedDeriv_succ]
        exact ih.deriv hopen
  have hrealU : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), (t:ℂ) ∈ U := by
    have hc : ContinuousAt (fun t : ℝ => (t:ℂ)) 0 := by fun_prop
    exact hc.tendsto (hopen.mem_nhds hz)
  have he (m : ℕ) : iteratedDeriv m (fun t : ℝ => (F (t:ℂ)).re) =ᶠ[𝓝 (0:ℝ)]
      fun t : ℝ => (iteratedDeriv m F (t:ℂ)).re := by
    induction m with
    | zero => simp
    | succ m ih =>
        have ih' := ih.deriv
        filter_upwards [ih',hrealU] with t ht hU
        simp only [iteratedDeriv_succ]
        rw [ht]
        have hlocal := (hall m).differentiableAt (hopen.mem_nhds hU)
        exact hlocal.hasDerivAt.real_of_complex.deriv
  exact (he n).eq_of_nhds

theorem displaced_green_response_analytic (d : ℝ)
    (ha : AnalyticAt ℂ completedNativeOperatorCharacteristic (displacedHeight d 0))
    (hne : completedSigmaResponse d 0 ≠ 0) :
    AnalyticAt ℂ centerGreenResponse (displacedHeight d 0) := by
  unfold centerGreenResponse completedGreenNormalizedResponse
  have hcomp : completedNativeOperatorBoundaryCompanion =
      fun z => -deriv completedNativeOperatorCharacteristic z := by
    funext z
    exact completedNativeOperatorBoundaryCompanion_eq_neg_deriv z
  rw [hcomp]
  exact ha.deriv.neg.div (analyticAt_const.mul ha) (mul_ne_zero (by norm_num) hne)

theorem displaced_log_deriv_eventually (d : ℝ)
    (ha : AnalyticAt ℂ completedNativeOperatorCharacteristic (displacedHeight d 0))
    (hne : completedSigmaResponse d 0 ≠ 0) :
    deriv (fun t : ℝ => Real.log (completedSigmaDensity d t)) =ᶠ[𝓝 (0:ℝ)]
      fun t : ℝ => -4*(centerGreenResponse (displacedHeight d t)).re := by
  have hnon : ∀ᶠ z : ℂ in 𝓝 (displacedHeight d 0), completedNativeOperatorCharacteristic z ≠ 0 :=
    ha.continuousAt.eventually_ne hne
  have hp : ContinuousAt (fun t : ℝ => displacedHeight d t) 0 := by
    unfold displacedHeight
    fun_prop
  have hnear := hp.tendsto (ha.eventually_analyticAt.and hnon)
  filter_upwards [hnear] with t ht
  have h := (log_density_hasDerivAt d t ht.1 ht.2).deriv
  rw [h]
  unfold centerGreenResponse completedGreenNormalizedResponse
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
  change 2*(deriv completedNativeOperatorCharacteristic (displacedHeight d t) /
      completedNativeOperatorCharacteristic (displacedHeight d t)).re =
    -4*(-deriv completedNativeOperatorCharacteristic (displacedHeight d t) /
      (2*completedNativeOperatorCharacteristic (displacedHeight d t))).re
  have he : -deriv completedNativeOperatorCharacteristic (displacedHeight d t) /
      (2*completedNativeOperatorCharacteristic (displacedHeight d t)) =
      -(1/2:ℂ)*(deriv completedNativeOperatorCharacteristic (displacedHeight d t) /
        completedNativeOperatorCharacteristic (displacedHeight d t)) := by
    field_simp [ht.2]
  rw [he]
  simp [Complex.mul_re]; ring

/-- The log-modulus jet and the original completed Green jet are equal at
any nonvanishing analytic displacement, with their given normalization. -/
theorem displaced_log_jet_eq_green (d : ℝ) (n : ℕ)
    (ha : AnalyticAt ℂ completedNativeOperatorCharacteristic (displacedHeight d 0))
    (hne : completedSigmaResponse d 0 ≠ 0) :
    completedSigmaLogJet d n = sigmaGreenMoment d n := by
  have hr := displaced_green_response_analytic d ha hne
  let shifted : ℂ → ℂ := fun z => centerGreenResponse (z - Complex.I*(d:ℂ))
  have hs : AnalyticAt ℂ shifted 0 := by
    have hr' : AnalyticAt ℂ centerGreenResponse (0 - Complex.I*(d:ℂ)) := by
      simpa [displacedHeight] using hr
    have hi : AnalyticAt ℂ (fun z : ℂ => z - Complex.I*(d:ℂ)) 0 := by fun_prop
    exact AnalyticAt.comp (f:=fun z : ℂ => z - Complex.I*(d:ℂ)) hr' hi
  have hre := analytic_real_iteratedDeriv_at_zero shifted hs (2*n+1)
  have hshift : iteratedDeriv (2*n+1) shifted 0 =
      iteratedDeriv (2*n+1) centerGreenResponse (-(Complex.I)*(d:ℂ)) := by
    unfold shifted
    rw [iteratedDeriv_comp_sub_const]
    simp
  rw [hshift] at hre
  have hre' : iteratedDeriv (2*n+1)
      (fun t : ℝ => (centerGreenResponse (displacedHeight d t)).re) 0 =
      (iteratedDeriv (2*n+1) centerGreenResponse (-(Complex.I)*(d:ℂ))).re := by
    simpa [shifted,displacedHeight] using hre
  unfold completedSigmaLogJet
  rw [show 2*n+2=(2*n+1)+1 by omega,iteratedDeriv_succ']
  rw [Filter.EventuallyEq.iteratedDeriv_eq (2*n+1) (displaced_log_deriv_eventually d ha hne)]
  rw [iteratedDeriv_const_mul_field,hre']
  unfold sigmaGreenMoment
  have hf : ((2*n+2).factorial:ℝ) = ((2*n+2:ℕ):ℝ)*((2*n+1).factorial:ℝ) := by
    rw [show 2*n+2=(2*n+1)+1 by omega,Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  push_cast
  field_simp
  ring

end
end CarrySigmaSource
