import SigmaParity
import CarrySelfAdjointOperator.CompletedNativeCentralChiralQuotientCurvature
import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace CarrySigmaSource
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

def centerRealSource (t : ℝ) : ℝ := (completedNativeOperatorCharacteristic (t:ℂ)).re

theorem center_real_source_hasDerivAt (t : ℝ) :
    HasDerivAt centerRealSource (deriv completedNativeOperatorCharacteristic (t:ℂ)).re t := by
  have h := (completedNativeOperatorCharacteristic_analyticAt
    (ofReal_mem_completedNativeHeightDomain t)).differentiableAt.hasDerivAt.real_of_complex
  exact h

theorem center_real_source_deriv : deriv centerRealSource =
    fun t : ℝ => (deriv completedNativeOperatorCharacteristic (t:ℂ)).re := by
  funext t
  exact (center_real_source_hasDerivAt t).deriv

theorem center_real_source_ne_zero : centerRealSource 0 ≠ 0 := by
  intro hzero
  apply completedNativeOperatorCharacteristic_zero_ne_zero
  have hi := completedNativeOperatorCharacteristic_ofReal_im_eq_zero 0
  apply Complex.ext
  · simpa [centerRealSource] using hzero
  · simpa using hi

theorem center_real_source_deriv_zero : deriv centerRealSource 0 = 0 := by
  rw [center_real_source_deriv]
  have h := deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
    completedNativeOperatorCharacteristic_eventually_even
  simp [h]

theorem center_real_source_second_deriv :
    HasDerivAt (deriv centerRealSource)
      (iteratedDeriv 2 completedNativeOperatorCharacteristic 0).re 0 := by
  rw [center_real_source_deriv]
  have hf : DifferentiableOn ℂ completedNativeOperatorCharacteristic completedNativeHeightDomain := by
    intro z hz
    exact (completedNativeOperatorCharacteristic_analyticAt hz).differentiableAt.differentiableWithinAt
  have hf' : DifferentiableAt ℂ (deriv completedNativeOperatorCharacteristic) 0 :=
    (hf.deriv isOpen_completedNativeHeightDomain).differentiableAt
      (isOpen_completedNativeHeightDomain.mem_nhds zero_mem_completedNativeHeightDomain)
  have hh := hf'.hasDerivAt.real_of_complex
  simpa [show (2:ℕ) = 1+1 by omega,iteratedDeriv_succ] using hh

theorem center_log_second_deriv :
    iteratedDeriv 2 (fun t => Real.log (centerRealSource t)) 0 =
      (iteratedDeriv 2 completedNativeOperatorCharacteristic 0).re / centerRealSource 0 := by
  have hne : ∀ᶠ t : ℝ in 𝓝 (0:ℝ), centerRealSource t ≠ 0 :=
    (center_real_source_hasDerivAt 0).continuousAt.eventually_ne center_real_source_ne_zero
  have heq : deriv (fun t => Real.log (centerRealSource t)) =ᶠ[𝓝 (0:ℝ)]
      (fun t => deriv centerRealSource t / centerRealSource t) := by
    filter_upwards [hne] with t ht
    exact deriv.log (center_real_source_hasDerivAt t).differentiableAt ht
  have hd := (center_real_source_second_deriv.div (center_real_source_hasDerivAt 0)
    center_real_source_ne_zero).deriv
  rw [show (2:ℕ)=1+1 by omega,iteratedDeriv_succ,iteratedDeriv_one,heq.deriv_eq]
  change deriv (fun t => deriv centerRealSource t / centerRealSource t) 0 = _ at hd
  have hs : (iteratedDeriv 2 completedNativeOperatorCharacteristic 0).re * centerRealSource 0 /
      centerRealSource 0^2 = (iteratedDeriv 2 completedNativeOperatorCharacteristic 0).re / centerRealSource 0 := by
    field_simp [center_real_source_ne_zero]
  simpa only [center_real_source_deriv_zero,mul_zero,zero_mul,sub_zero,hs,Pi.div_apply] using hd

theorem sigma_log_jet_zero_eq_canonical :
    completedSigmaLogJet 0 0 = canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [sigma_log_jet_center_formula]
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.factorial, Nat.cast_ofNat, Nat.cast_one]
  rw [show (fun t : ℝ => Real.log ((completedNativeOperatorCharacteristic (t:ℂ)).re)) =
    (fun t : ℝ => Real.log (centerRealSource t)) from rfl, center_log_second_deriv]
  have hf : completedNativeOperatorCharacteristic 0 = (centerRealSource 0:ℂ) := by
    have hi := completedNativeOperatorCharacteristic_ofReal_im_eq_zero 0
    apply Complex.ext
    · simp [centerRealSource]
    · change (completedNativeOperatorCharacteristic 0).im = 0
      simpa only [Complex.ofReal_zero] using hi
  have hm := canonicalCompletedNativeLogDerivativeMoment_zero_eq_characteristicCurvature_chiral
  rw [hf] at hm
  have hd : (2:ℂ)*(centerRealSource 0:ℂ) = ((2*centerRealSource 0:ℝ):ℂ) := by push_cast; ring
  rw [hd] at hm
  have hr := congrArg Complex.re hm
  simp only [Complex.ofReal_re,Complex.div_ofReal_re,Complex.neg_re] at hr
  rw [hr]
  field_simp [center_real_source_ne_zero]

end
end CarrySigmaSource
