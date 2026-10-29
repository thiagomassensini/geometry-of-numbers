import OddRegression
import CarrySelfAdjointOperator.NativeCompletedCenteredReflection
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.CompMul

namespace CarryMixedParity
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Merely the original characteristic in the already used imaginary chart. -/
def rotatedCharacteristic (z : ℂ) : ℂ := completedNativeOperatorCharacteristic (Complex.I*z)

/-- Direct native-channel reflection, with its original completion factor. -/
theorem rotated_characteristic_reflection (z : ℂ) :
    rotatedCharacteristic (conj z)=conj (rotatedCharacteristic z) := by
  have h := completedNativeOperatorCharacteristic_neg_conj_from_nativeChannel (Complex.I*z)
  simpa [rotatedCharacteristic, map_mul, Complex.conj_I] using h

theorem rotated_derivative_reflection (z : ℂ) :
    deriv rotatedCharacteristic (conj z)=conj (deriv rotatedCharacteristic z) := by
  have he : (conj ∘ rotatedCharacteristic ∘ conj)=rotatedCharacteristic := by
    funext w
    simpa [Function.comp_def] using (rotated_characteristic_reflection (conj w)).symm
  have hd := congrArg (fun f : ℂ → ℂ => deriv f (conj z)) he
  simpa using hd.symm

/-- Identity of the SAME totalized response, without a positive measure. -/
theorem response_rotated_derivative (z : ℂ) :
    responseReadout z=deriv rotatedCharacteristic z/(2*rotatedCharacteristic z) := by
  unfold responseReadout completedGreenNormalizedResponse rotatedCharacteristic
  rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv, deriv_comp_mul_left]
  simp only [smul_eq_mul]
  ring

theorem response_reflection (z : ℂ) :
    responseReadout (conj z)=conj (responseReadout z) := by
  rw [response_rotated_derivative, response_rotated_derivative,
    rotated_derivative_reflection, rotated_characteristic_reflection]
  simp only [map_div₀, map_mul, map_ofNat]

theorem response_real_ray (t : ℝ) : conj (responseReadout (t:ℂ))=responseReadout (t:ℂ) := by
  simpa only [Complex.conj_ofReal] using (response_reflection (t:ℂ)).symm

theorem response_samples_real (t : ℝ) (j : ℕ) :
    conj (responseSamples (t:ℂ) j)=responseSamples (t:ℂ) j := by
  have h := response_real_ray (((j+1:ℕ):ℝ)*t)
  simpa only [responseSamples, Complex.ofReal_mul, Complex.ofReal_natCast] using h

theorem static_stencil_real (m j : ℕ) : conj (staticStencil m j)=staticStencil m j := by
  simp [staticStencil, Finsupp.smul_apply, smul_eq_mul, raw_stencil_apply,
    completedGreenForwardWeight]

theorem even_coefficients_real (S : Finset ℕ) (c : ℕ → ℝ) (k j : ℕ) :
    conj (finiteJetSource S c k j)=finiteJetSource S c k j := by
  simp only [finite_source_profile, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  simp [nativeEvenProfile, Finsupp.smul_apply, smul_eq_mul, static_stencil_real]

theorem odd_coefficients_imaginary (S : Finset ℕ) (c : ℕ → ℝ) (k j : ℕ) :
    conj (finiteOddJetSource S c k j)= -finiteOddJetSource S c k j := by
  simp only [finite_odd_source_profile, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, map_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [nativeOddProfile, Finsupp.smul_apply, smul_eq_mul, map_mul, map_neg,
    map_pow, map_one, map_add, map_natCast, Complex.conj_I, Complex.conj_ofReal,
    static_stencil_real]
  ring

theorem kernel_smul_left (w : ℕ → ℂ) (a : ℂ) (c d : ℕ →₀ ℂ) :
    kernel w (a • c) d=conj a*kernel w c d := by
  simpa only [one_smul, mul_one] using kernel_scale_inputs w a 1 c d

theorem kernel_smul_right (w : ℕ → ℂ) (a : ℂ) (c d : ℕ →₀ ℂ) :
    kernel w c (a • d)=a*kernel w c d := by
  simpa only [one_smul, map_one, one_mul] using kernel_scale_inputs w 1 a c d

/-- Complete complex Cauchy pairing of arbitrary finite original inputs. -/
theorem kernel_double_sum (w : ℕ → ℂ) (c d : ℕ →₀ ℂ) :
    kernel w c d=∑ i ∈ c.support, ∑ j ∈ d.support,
      conj (c i)*w j*d j/((i:ℂ)+(j:ℂ)+2) := by
  have hs : physicalCauchySynthesis c=∑ i ∈ c.support,
      c i • completedNativeChiralCauchyFeature i := by
    rw [physicalCauchySynthesis, Finsupp.linearCombination_apply]
    rfl
  change inner ℂ (physicalCauchySynthesis c)
    (physicalCauchySynthesis (coefficientWeight w d))=_
  rw [hs, weighted_synthesis_sum]
  simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    inner_completedNativeChiralCauchyFeature]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem kernel_real_imaginary (w : ℕ → ℂ) (c d : ℕ →₀ ℂ)
    (hw : ∀ j, conj (w j)=w j) (hc : ∀ j, conj (c j)=c j)
    (hd : ∀ j, conj (d j)= -d j) : conj (kernel w c d)= -kernel w c d := by
  rw [kernel_double_sum]
  simp only [map_sum, map_div₀, map_mul, map_add, map_natCast, map_ofNat]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [hw, hc, hd]
  ring

theorem kernel_imaginary_real (w : ℕ → ℂ) (c d : ℕ →₀ ℂ)
    (hw : ∀ j, conj (w j)=w j) (hc : ∀ j, conj (c j)= -c j)
    (hd : ∀ j, conj (d j)=d j) : conj (kernel w c d)= -kernel w c d := by
  rw [kernel_double_sum]
  simp only [map_sum, map_div₀, map_mul, map_add, map_natCast, map_ofNat]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [hw, hc, hd, map_neg, neg_neg]
  ring

end
end CarryMixedParity
