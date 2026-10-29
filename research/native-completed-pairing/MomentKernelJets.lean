import CompletedChannels
import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceLimit

/-! The response is read from the completed SOURCE, before canonical
moments enter any statement. Its divided difference has the canonical
mixed coefficients. This is a scalar kernel identification, not a Gram. -/
namespace CarryCompletedPairing
open CarryCameraTail CarryMaterialTheta CarryFourLeg CarryGreenProvenance
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter
open scoped ComplexConjugate Topology
noncomputable section
set_option autoImplicit false

def mellinResponse (M : ℕ) (z : ℂ) : ℂ :=
  completedIntegralPairing (M+1) (M+1) z 0 /
    (2 * completedNativeOperatorCharacteristic z * conj (completedNativeOperatorCharacteristic 0))

theorem mellin_response_eventuallyEq (M : ℕ) :
    mellinResponse M =ᶠ[nhds 0]
      completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion := by
  have hdomain : completedNativeHeightDomain ∈ nhds (0 : ℂ) :=
    isOpen_completedNativeHeightDomain.mem_nhds zero_mem_completedNativeHeightDomain
  have htfvd : mellinResponse M =ᶠ[nhds 0] canonicalC3BracketTfvdNormalizedResponse M := by
    filter_upwards [hdomain] with z hz
    unfold mellinResponse canonicalC3BracketTfvdNormalizedResponse
    rw [completed_pairing_mellin (M+1) z 0 hz.1
      (show 0 < (operatorHeightParameter 0).re by norm_num [operatorHeightParameter])]
  exact htfvd.trans (canonicalC3BracketTfvdNormalizedResponse_eventuallyEq_completed M)

theorem mellin_response_analyticAt (M : ℕ) : AnalyticAt ℂ (mellinResponse M) 0 :=
  completedNativeGreenNormalizedResponse_analyticAt.congr (mellin_response_eventuallyEq M).symm

/-- Holomorphic two-endpoint divided difference of the actual source
response. Physical conjugate-first sampling uses a conjugated first
endpoint; on the real sampling grids used below they coincide. -/
def mellinMomentKernel (M : ℕ) (w z : ℂ) : ℂ := dslope (mellinResponse M) w z

theorem completed_pairing_normalized (M N : ℕ) {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic z ≠ 0)
    (hwF : completedNativeOperatorCharacteristic w ≠ 0) :
    completedIntegralPairing M N z w /
        (2 * completedNativeOperatorCharacteristic z * conj (completedNativeOperatorCharacteristic w)) =
      completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z -
      conj (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion w) := by
  rw [completed_pairing_eq_original M N hz hw]
  unfold completedGreenWronskian completedGreenNormalizedResponse
  simp only [map_div₀, map_mul, map_ofNat]
  have hwStar : conj (completedNativeOperatorCharacteristic w) ≠ 0 := by simpa using hwF
  field_simp

theorem mellin_response_on_domain (M : ℕ) {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) :
    mellinResponse M z = completedGreenNormalizedResponse completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion z := by
  unfold mellinResponse
  rw [completed_pairing_eq_original (M+1) (M+1) hz zero_mem_completedNativeHeightDomain]
  have hc : completedNativeOperatorBoundaryCompanion 0 = 0 := by
    rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv,
      deriv_zero_of_eventually_even completedNativeOperatorCharacteristic
        completedNativeOperatorCharacteristic_eventually_even]
    simp
  unfold completedGreenWronskian completedGreenNormalizedResponse
  rw [hc]
  simp only [map_zero, mul_zero, sub_zero]
  by_cases hf : completedNativeOperatorCharacteristic z = 0
  · simp [hf]
  · have hzero : conj (completedNativeOperatorCharacteristic 0) ≠ 0 := by
      simpa using completedNativeOperatorCharacteristic_zero_ne_zero
    field_simp

/-- Off the diagonal on the real height axis, the two-point kernel is
literally the completed integral pairing divided by its ORIGINAL response
normalization and endpoint difference. The collision is filled by dslope,
not by setting an indeterminate quotient to zero. -/
theorem moment_kernel_from_completed_pairing (M : ℕ) (x y : ℝ) (hxy : y ≠ x)
    (hxF : completedNativeOperatorCharacteristic (x : ℂ) ≠ 0)
    (hyF : completedNativeOperatorCharacteristic (y : ℂ) ≠ 0) :
    mellinMomentKernel M (x : ℂ) (y : ℂ) =
      completedIntegralPairing M M (y : ℂ) (x : ℂ) /
        (2 * completedNativeOperatorCharacteristic (y : ℂ) *
          conj (completedNativeOperatorCharacteristic (x : ℂ)) * ((y : ℂ)-(x : ℂ))) := by
  have hx : operatorHeightParameter (x : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have hy : operatorHeightParameter (y : ℂ) ∈ genuineCriticalStrip := by
    constructor <;> norm_num [operatorHeightParameter]
  have hcast : (y : ℂ) ≠ (x : ℂ) := by exact_mod_cast hxy
  unfold mellinMomentKernel
  rw [dslope_of_ne _ hcast]
  unfold slope
  rw [mellin_response_on_domain M hx, mellin_response_on_domain M hy]
  have hp := completed_pairing_normalized M M hy hx hyF hxF
  rw [completedNativeGreenNormalizedResponse_ofReal_conj x] at hp
  simp only [vsub_eq_sub]
  rw [← hp]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- All mixed coefficient limits, derived from the source response and
the existing analytic divided-difference theorem. No Hilbert Gram or
Hankel positivity hypothesis is used. -/
theorem mellin_mixed_jets (M p q : ℕ) :
    Tendsto (fun k => completedGreenKernelForwardDifference
      (mellinMomentKernel M) (canonicalGreenJetStep k) p q) atTop
      (nhds (polarizedGreenMomentCoefficient canonicalCompletedNativeLogDerivativeMoment p q)) := by
  have h := completedGreenKernelForwardDifference_dslope_tendsto
    (mellin_response_analyticAt M) p q
  have hderiv := (mellin_response_eventuallyEq M).iteratedDeriv_eq (p+q+1)
  rw [hderiv] at h
  have hc := completedNativeGreenResponseTaylorCoefficient_succ_eq_polarized p q
  change iteratedDeriv (p+q+1)
      (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion) 0 / ((p+q+1).factorial : ℂ) = _ at hc
  rw [hc] at h
  exact h

theorem mellin_even_jets (M i j : ℕ) :
    Tendsto (fun k => completedGreenKernelForwardDifference
      (mellinMomentKernel M) (canonicalGreenJetStep k) (2*i) (2*j)) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment (i+j) : ℂ)) := by
  have h := mellin_mixed_jets M (2*i) (2*j)
  have he : Even (2*i+2*j) := ⟨i+j, by omega⟩
  have hd : (2*i+2*j)/2 = i+j := by omega
  simpa only [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient, if_pos he, hd] using h

theorem mellin_shifted_jets (M i j : ℕ) :
    Tendsto (fun k => completedGreenKernelForwardDifference
      (mellinMomentKernel M) (canonicalGreenJetStep k) (2*i+1) (2*j+1)) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment (i+j+1) : ℂ)) := by
  have h := mellin_mixed_jets M (2*i+1) (2*j+1)
  have he : Even (2*i+1+(2*j+1)) := ⟨i+j+1, by omega⟩
  have hd : (2*i+1+(2*j+1))/2 = i+j+1 := by omega
  simpa only [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient, if_pos he, hd] using h

theorem mellin_even_odd_jets_zero (M i j : ℕ) :
    Tendsto (fun k => completedGreenKernelForwardDifference
      (mellinMomentKernel M) (canonicalGreenJetStep k) (2*i) (2*j+1)) atTop (nhds 0) := by
  have h := mellin_mixed_jets M (2*i) (2*j+1)
  have he : ¬ Even (2*i+(2*j+1)) := by rintro ⟨k,hk⟩; omega
  simpa only [polarizedGreenMomentCoefficient, evenMomentDiagonalCoefficient, if_neg he] using h

theorem mellin_jet_00 (M : ℕ) :
    Tendsto (fun k => completedGreenKernelForwardDifference
      (mellinMomentKernel M) (canonicalGreenJetStep k) 0 0) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) := by
  exact mellin_even_jets M 0 0

theorem mellin_jet_01 (M : ℕ) :
    Tendsto (fun k => completedGreenKernelForwardDifference
      (mellinMomentKernel M) (canonicalGreenJetStep k) 0 2) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)) := by
  exact mellin_even_jets M 0 1

theorem mellin_jet_11 (M : ℕ) :
    Tendsto (fun k => completedGreenKernelForwardDifference
      (mellinMomentKernel M) (canonicalGreenJetStep k) 2 2) atTop
      (nhds (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ)) := by
  exact mellin_even_jets M 1 1

end
end CarryCompletedPairing
