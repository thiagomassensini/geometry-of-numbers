import DerivativeLedger
import CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments

/-!
# Cancelamento transversal da síntese C3 completada

A resposta transversal do estado completado é comparada à decomposição exata
em tilt, complemento carrier/cruzamentos e multiplicador original. A paridade
já demonstrada da característica implica o cancelamento dos jets mistos de
ordem par em altura. No centro, o termo compensador é não nulo.

Esses resultados dizem respeito ao readout da síntese completa; não provam uma
representação Gram dos momentos canônicos, sinal dos pivôs ou sinal all-order.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

def fullTransverseResponse (t : ℝ) : ℂ :=
  deriv (fun d : ℝ => completedNativeOperatorCharacteristic ((t : ℂ) - Complex.I * (d : ℂ))) 0

theorem fullTransverseResponse_eq (t : ℝ) :
    fullTransverseResponse t = -Complex.I *
      deriv (fun u : ℝ => completedNativeOperatorCharacteristic (u : ℂ)) t := by
  have hmem : (t:ℂ) ∈ completedNativeHeightDomain := by
    change operatorHeightParameter (t:ℂ) ∈ genuineCriticalStrip
    constructor <;> norm_num [operatorHeightParameter]
  have hf := (completedNativeOperatorCharacteristic_analyticAt hmem).differentiableAt.hasDerivAt
  have hg : HasDerivAt (fun z : ℂ => (t:ℂ) - Complex.I * z) (-Complex.I) 0 := by
    have h := (hasDerivAt_const (0:ℂ) (t:ℂ)).sub ((hasDerivAt_id (0:ℂ)).const_mul Complex.I)
    have hderiv : 0 - Complex.I * 1 = -Complex.I := by ring
    have h := h.congr_deriv hderiv
    exact h
  have hf' : HasDerivAt completedNativeOperatorCharacteristic
      (deriv completedNativeOperatorCharacteristic (t:ℂ)) ((t:ℂ) - Complex.I * 0) := by simpa using hf
  have hcomp := (hf'.comp (0:ℂ) hg).comp_ofReal
  have hval : HasDerivAt (fun d : ℝ => completedNativeOperatorCharacteristic ((t:ℂ) - Complex.I * (d:ℂ)))
      (deriv completedNativeOperatorCharacteristic (t:ℂ) * (-Complex.I)) 0 := by
    simpa only [Function.comp_def,Complex.ofReal_zero,mul_zero,sub_zero] using hcomp
  unfold fullTransverseResponse
  rw [hval.deriv]
  have hr := iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal 1 t
  simp only [iteratedDeriv_one] at hr
  rw [hr]
  ring

theorem fullTransverseResponse_even_jet_zero (n : ℕ) :
    iteratedDeriv (2*n) fullTransverseResponse 0 = 0 := by
  have heq : fullTransverseResponse = fun t : ℝ => -Complex.I *
      deriv (fun u : ℝ => completedNativeOperatorCharacteristic (u:ℂ)) t := by
    funext t; exact fullTransverseResponse_eq t
  rw [heq, iteratedDeriv_const_mul_field, ← iteratedDeriv_succ']
  have h := iteratedDeriv_completedNativeOperatorCharacteristic_comp_ofReal (2*n+1) 0
  simp only [Complex.ofReal_zero] at h
  rw [h, iteratedDeriv_completedNativeOperatorCharacteristic_odd_zero]
  simp

theorem analytic_transverse_hasDerivAt (f : ℂ → ℂ) (t : ℝ) (hf : AnalyticAt ℂ f (t:ℂ)) :
    HasDerivAt (fun d : ℝ => f ((t:ℂ) - Complex.I * (d:ℂ)))
      (-Complex.I * deriv f (t:ℂ)) 0 := by
  have hg : HasDerivAt (fun z : ℂ => (t:ℂ) - Complex.I * z) (-Complex.I) 0 := by
    have h := (hasDerivAt_const (0:ℂ) (t:ℂ)).sub ((hasDerivAt_id (0:ℂ)).const_mul Complex.I)
    have hderiv : 0 - Complex.I * 1 = -Complex.I := by ring
    exact h.congr_deriv hderiv
  have hf' : HasDerivAt f (deriv f (t:ℂ)) ((t:ℂ) - Complex.I * 0) := by
    simpa using hf.differentiableAt.hasDerivAt
  have h := (hf'.comp (0:ℂ) hg).comp_ofReal
  have h' : HasDerivAt (fun d : ℝ => f ((t:ℂ) - Complex.I * (d:ℂ)))
      (deriv f (t:ℂ) * (-Complex.I)) 0 := by
    simpa only [Function.comp_def,Complex.ofReal_zero,mul_zero,sub_zero] using h
  exact h'.congr_deriv (by ring)

def completionRemainderResponse (t : ℝ) : ℂ :=
  (-Complex.I * deriv CarryTwoEvenJets.valueMultiplier (t:ℂ)) *
     (1 + infiniteCarrierRemainder t 0) +
    CarryTwoEvenJets.valueMultiplier (t:ℂ) * deriv (infiniteCarrierRemainder t) 0

theorem fullTransverseResponse_eq_channels (t : ℝ)
    (hv : AnalyticAt ℂ CarryTwoEvenJets.valueMultiplier (t:ℂ)) :
    fullTransverseResponse t =
      CarryTwoEvenJets.valueMultiplier (t:ℂ) * infiniteMixedTiltResponse (t:ℂ) +
        completionRemainderResponse t := by
  have hprod := (analytic_transverse_hasDerivAt CarryTwoEvenJets.valueMultiplier t hv).mul
    (((hasDerivAt_const (0:ℝ) (1:ℂ)).add (hasDerivAt_infiniteTransverseTilt t)).add
      (infiniteCarrierRemainder_hasDerivAt t))
  have heq : (fun d : ℝ => completedNativeOperatorCharacteristic ((t:ℂ)-Complex.I*(d:ℂ))) =ᶠ[𝓝 (0:ℝ)]
      (fun d : ℝ => CarryTwoEvenJets.valueMultiplier ((t:ℂ)-Complex.I*(d:ℂ)) *
         (1 + infiniteTransverseTilt t d + infiniteCarrierRemainder t d)) := by
    have hi : Set.Ioo (-(1/4:ℝ)) (1/4:ℝ) ∈ 𝓝 (0:ℝ) := isOpen_Ioo.mem_nhds (by norm_num)
    filter_upwards [hi] with d hd
    exact completed_parameter_decomposition t d hd.1 hd.2
  have hcomp := hprod.congr_of_eventuallyEq heq
  unfold fullTransverseResponse completionRemainderResponse
  rw [hcomp.deriv, (infiniteCarrierRemainder_hasDerivAt t).deriv]
  simp only [Pi.add_apply, infiniteTransverseTilt_zero, Complex.ofReal_zero, mul_zero, sub_zero, add_zero, zero_add]
  ring

theorem full_channels_even_jet_cancel (n : ℕ) :
    iteratedDeriv (2*n) (fun t : ℝ =>
      CarryTwoEvenJets.valueMultiplier (t:ℂ) * infiniteMixedTiltResponse (t:ℂ) +
        completionRemainderResponse t) 0 = 0 := by
  have hv : ∀ᶠ t : ℝ in 𝓝 0, AnalyticAt ℂ CarryTwoEvenJets.valueMultiplier (t:ℂ) := by
    have hh := CarryTwoEvenJets.valueMultiplier_analytic.eventually_analyticAt
    exact (Complex.continuous_ofReal.continuousAt.tendsto).eventually (by simpa using hh)
  have heq : fullTransverseResponse =ᶠ[𝓝 (0:ℝ)] (fun t : ℝ =>
      CarryTwoEvenJets.valueMultiplier (t:ℂ) * infiniteMixedTiltResponse (t:ℂ) +
        completionRemainderResponse t) := by
    filter_upwards [hv] with t ht
    exact fullTransverseResponse_eq_channels t ht
  rw [← heq.iteratedDeriv_eq]
  exact fullTransverseResponse_even_jet_zero n

theorem center_exact_cancellation :
    completionRemainderResponse 0 =
      -(CarryTwoEvenJets.valueMultiplier 0 * infiniteMixedTiltResponse 0) := by
  have h := full_channels_even_jet_cancel 0
  simp only [Nat.mul_zero, iteratedDeriv_zero, Complex.ofReal_zero] at h
  linear_combination h

theorem center_multiplier_ne_zero : CarryTwoEvenJets.valueMultiplier 0 ≠ 0 := by
  intro h
  have hf := completed_parameter_decomposition 0 0 (by norm_num) (by norm_num)
  simp only [Complex.ofReal_zero, mul_zero, sub_zero, h, zero_mul] at hf
  exact completedNativeOperatorCharacteristic_zero_ne_zero hf

theorem center_tiltResponse_ne_zero : infiniteMixedTiltResponse 0 ≠ 0 := by
  have hp := infinite_mixed_tilt_positive 0
  simp only [Nat.mul_zero, pow_zero, iteratedDeriv_zero, one_mul, Complex.ofReal_zero] at hp
  intro h
  rw [h] at hp
  norm_num at hp

theorem center_completionRemainder_ne_zero : completionRemainderResponse 0 ≠ 0 := by
  rw [center_exact_cancellation]
  exact neg_ne_zero.mpr (mul_ne_zero center_multiplier_ne_zero center_tiltResponse_ne_zero)

#print axioms center_exact_cancellation
#print axioms center_completionRemainder_ne_zero
#print axioms fullTransverseResponse_even_jet_zero
#print axioms fullTransverseResponse_eq_channels
#print axioms full_channels_even_jet_cancel
end
end CarryTiltSlice
