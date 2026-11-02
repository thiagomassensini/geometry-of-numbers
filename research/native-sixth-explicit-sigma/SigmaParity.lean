import CarrySelfAdjointOperator.NativeCompletedCenteredReflection
import CarrySelfAdjointOperator.CompletedNativeRealWeylMoments
import CarrySelfAdjointOperator.CompletedGreenMomentJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace CarrySigmaSource
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Literal coordinate of the original completed characteristic: the real
part of the physical parameter is 1/2 + d, its height is t. -/
def displacedHeight (d t : ℝ) : ℂ := (t:ℂ) - Complex.I*(d:ℂ)

def completedSigmaResponse (d t : ℝ) : ℂ :=
  completedNativeOperatorCharacteristic (displacedHeight d t)

def completedSigmaDensity (d t : ℝ) : ℝ := ‖completedSigmaResponse d t‖^2

/-- Taylor-jet readout of the actual completed modulus squared. This definition
is not claimed here to be identified with the canonical recurrence. -/
def completedSigmaLogJet (d : ℝ) (n : ℕ) : ℝ :=
  -((n+1:ℕ):ℝ)/(2*((2*n+2).factorial:ℝ)) *
    iteratedDeriv (2*n+2) (fun t : ℝ => Real.log (completedSigmaDensity d t)) 0

theorem displacedHeight_parameter (d t : ℝ) :
    operatorHeightParameter (displacedHeight d t) = ((1/2+d:ℝ):ℂ) + Complex.I*(t:ℂ) := by
  apply Complex.ext <;> simp [operatorHeightParameter,displacedHeight]

theorem displacedHeight_strip (d t : ℝ) (hd₁ : -(1/2:ℝ)<d) (hd₂ : d<(1/2:ℝ)) :
    operatorHeightParameter (displacedHeight d t) ∈ genuineCriticalStrip := by
  rw [displacedHeight_parameter]
  constructor <;> simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_self,add_zero] <;> linarith

theorem sigma_response_central_axis (t : ℝ) :
    completedSigmaResponse 0 t = completedNativeOperatorCharacteristic (t:ℂ) := by
  simp [completedSigmaResponse,displacedHeight]

/-- At the center the two real quadratures of the completed response are
recombined before reading the squared norm. -/
theorem sigma_density_center (t : ℝ) :
    completedSigmaDensity 0 t = (completedNativeOperatorCharacteristic (t:ℂ)).re^2 := by
  unfold completedSigmaDensity
  rw [sigma_response_central_axis]
  have hi := completedNativeOperatorCharacteristic_ofReal_im_eq_zero t
  have he : completedNativeOperatorCharacteristic (t:ℂ) =
      ((completedNativeOperatorCharacteristic (t:ℂ)).re:ℂ) := by
    apply Complex.ext <;> simp [hi]
  rw [he]
  simp [Complex.norm_real,Real.norm_eq_abs,sq_abs]

/-- Central log-modulus jets reduce exactly to real log jets of the very
same completed characteristic. Identification with the canonical recurrence
is a separate obligation. -/
theorem sigma_log_jet_center_formula (n : ℕ) :
    completedSigmaLogJet 0 n = -((n+1:ℕ):ℝ)/(((2*n+2).factorial:ℝ)) *
      iteratedDeriv (2*n+2)
        (fun t : ℝ => Real.log ((completedNativeOperatorCharacteristic (t:ℂ)).re)) 0 := by
  have he : (fun t : ℝ => Real.log (completedSigmaDensity 0 t)) =
      (fun t : ℝ => (2:ℝ)*Real.log ((completedNativeOperatorCharacteristic (t:ℂ)).re)) := by
    funext t
    rw [sigma_density_center,Real.log_pow]
    norm_num
  unfold completedSigmaLogJet
  rw [he,iteratedDeriv_const_mul_field]
  ring

theorem sigma_response_conjugate (d t : ℝ) (hd₁ : -(1/2:ℝ)<d) (hd₂ : d<(1/2:ℝ)) :
    completedSigmaResponse (-d) t = (starRingEnd ℂ) (completedSigmaResponse d t) := by
  have hz := completedNativeOperatorCharacteristic_neg (displacedHeight_strip (-d) t (by linarith) (by linarith))
  have hc := completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel (displacedHeight d t)
  have hneg : -(displacedHeight (-d) t) = -(starRingEnd ℂ) (displacedHeight d t) := by
    apply Complex.ext <;> simp [displacedHeight]
  unfold completedSigmaResponse
  rw [hneg] at hz
  exact hz.symm.trans hc

theorem sigma_density_even (d t : ℝ) (hd₁ : -(1/2:ℝ)<d) (hd₂ : d<(1/2:ℝ)) :
    completedSigmaDensity (-d) t = completedSigmaDensity d t := by
  unfold completedSigmaDensity
  rw [sigma_response_conjugate d t hd₁ hd₂]
  simp

theorem sigma_log_jet_even (d : ℝ) (hd₁ : -(1/2:ℝ)<d) (hd₂ : d<(1/2:ℝ)) (n : ℕ) :
    completedSigmaLogJet (-d) n = completedSigmaLogJet d n := by
  have he : (fun t : ℝ => Real.log (completedSigmaDensity (-d) t)) =
      (fun t : ℝ => Real.log (completedSigmaDensity d t)) := by
    funext t
    rw [sigma_density_even d t hd₁ hd₂]
  unfold completedSigmaLogJet
  rw [he]

/-- If the log jet is differentiable in the displacement, the proved local
parity forces its first sigma derivative to vanish at the center. -/
theorem sigma_log_jet_deriv_zero (n : ℕ)
    (hdiff : DifferentiableAt ℝ (fun d => completedSigmaLogJet d n) 0) :
    deriv (fun d => completedSigmaLogJet d n) 0 = 0 := by
  let g : ℝ → ℝ := fun d => completedSigmaLogJet d n
  have hg : HasDerivAt g (deriv g 0) 0 := hdiff.hasDerivAt
  have hminus : HasDerivAt (fun d : ℝ => -d) (-1) 0 := by
    simpa only [id_eq,zero_sub] using (hasDerivAt_id (0:ℝ)).const_sub 0
  have hn : HasDerivAt (fun d : ℝ => g (-d)) (-(deriv g 0)) 0 := by
    have h := HasDerivAt.comp (0:ℝ)
      (show HasDerivAt g (deriv g 0) (-0) by simpa only [neg_zero] using hg) hminus
    simpa only [Function.comp_def,neg_one_mul,mul_neg_one] using h
  have he : (fun d : ℝ => g (-d)) =ᶠ[𝓝 (0:ℝ)] g := by
    have hm : Set.Ioo (-(1/2:ℝ)) (1/2:ℝ) ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [hm] with d hd
    exact sigma_log_jet_even d hd.1 hd.2 n
  have hne := hn.congr_of_eventuallyEq he.symm
  have hh := hg.unique hne
  change deriv g 0 = 0
  linarith

theorem completed_source_eventually_ne_zero :
    ∀ᶠ z : ℂ in 𝓝 (0:ℂ), completedNativeOperatorCharacteristic z ≠ 0 :=
  by
    have hz : (0:ℂ) ∈ completedNativeHeightDomain := ofReal_mem_completedNativeHeightDomain 0
    exact (completedNativeOperatorCharacteristic_analyticAt hz).differentiableAt.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero

end
end CarrySigmaSource
