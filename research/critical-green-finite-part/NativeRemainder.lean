import CriticalKernel

namespace CarryGreenFinitePart
open CarryInteriorGreen CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- A readout of the SAME completed response, after the original synthesis.
This is not a newly chosen physical source. -/
def imaginaryReadout (t : ℂ) : ℂ := -Complex.I*nativeResponse (Complex.I*t)

def readoutCoefficient (n : ℕ) : ℂ :=
  -Complex.I*Complex.I^n*completedNativeGreenResponseTaylorCoefficient n

theorem readout_analytic : AnalyticAt ℂ imaginaryReadout 0 := by
  have h := completedNativeGreenNormalizedResponse_analyticAt.fun_comp_of_eq
    (show AnalyticAt ℂ (fun t : ℂ => Complex.I*t) 0 by fun_prop) (by simp)
  exact analyticAt_const.mul h

theorem readout_coefficient_derivative (n : ℕ) :
    iteratedDeriv n imaginaryReadout 0/(n.factorial : ℂ)=readoutCoefficient n := by
  unfold imaginaryReadout readoutCoefficient completedNativeGreenResponseTaylorCoefficient
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_comp_mul_zero]
  ring

theorem readout_coefficient_even (j : ℕ) : readoutCoefficient (2*j)=0 := by
  simp [readoutCoefficient,completedNativeGreenResponseTaylorCoefficient_even_eq_zero]

theorem readout_coefficient_odd (j : ℕ) :
    readoutCoefficient (2*j+1)=(-1 : ℂ)^j*(canonicalCompletedNativeLogDerivativeMoment j : ℂ) := by
  rw [readoutCoefficient,completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  rw [pow_add,show Complex.I^(2*j)=(-1 : ℂ)^j by rw [pow_mul,Complex.I_sq]]
  ring_nf
  norm_num [Complex.I_sq]

/-- Exact Taylor sewing of the native response, retaining the eleventh-order
analytic remainder. No moment sign or finite positivity certificate is used. -/
theorem readout_exact_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ t : ℂ in nhds 0,
      imaginaryReadout t=(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*t-
        (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)*t^3+
        (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ)*t^5-
        (canonicalCompletedNativeLogDerivativeMoment 3 : ℂ)*t^7+
        (canonicalCompletedNativeLogDerivativeMoment 4 : ℂ)*t^9+t^11*R t := by
  obtain ⟨R,hRa,he⟩ := readout_analytic.exists_eventuallyEq_sum_add_pow_mul 11
  refine ⟨R,hRa,?_⟩
  filter_upwards [he] with t ht
  rw [ht]
  have hp : (∑ n ∈ Finset.range 11, (t^n/(n.factorial : ℂ)) • iteratedDeriv n imaginaryReadout 0)=
      ∑ n ∈ Finset.range 11, readoutCoefficient n*t^n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [← readout_coefficient_derivative]
    simp only [smul_eq_mul]
    ring
  rw [hp]
  simp only [smul_eq_mul]
  have h0 := readout_coefficient_even 0
  have h1 := readout_coefficient_odd 0
  have h2 := readout_coefficient_even 1
  have h3 := readout_coefficient_odd 1
  have h4 := readout_coefficient_even 2
  have h5 := readout_coefficient_odd 2
  have h6 := readout_coefficient_even 3
  have h7 := readout_coefficient_odd 3
  have h8 := readout_coefficient_even 4
  have h9 := readout_coefficient_odd 4
  have h10 := readout_coefficient_even 5
  norm_num only at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]
  ring

theorem readout_real (t : ℝ) : (imaginaryReadout (t : ℂ)).re=
    (nativeResponse (Complex.I*(t : ℂ))).im := by
  simp [imaginaryReadout,Complex.mul_re]

def radialStep (k : ℕ) : ℝ := ((k : ℝ)+1)⁻¹

theorem radial_step_limit : Tendsto radialStep atTop (nhds 0) := inverse_radial_mass_limit

theorem radial_node_readout (k j : ℕ) :
    (nativeResponse (canonicalCompletedC3RadialTiltPoint k j)).im=
      (imaginaryReadout (((j+1 : ℕ) : ℂ)*(radialStep k : ℂ))).re := by
  have hp : canonicalCompletedC3RadialTiltPoint k j=
      Complex.I*(((j+1 : ℕ) : ℂ)*(radialStep k : ℂ)) := by
    rw [canonicalCompletedC3RadialTiltPoint_eq_I_mul_im]
    simp only [canonicalCompletedC3RadialTiltPoint_im,radialStep]
    push_cast
    ring
  rw [hp]
  simp [imaginaryReadout,Complex.mul_re]

end
end CarryGreenFinitePart
