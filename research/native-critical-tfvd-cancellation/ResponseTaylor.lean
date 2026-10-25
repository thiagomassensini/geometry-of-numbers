import CriticalVectors
import CarrySelfAdjointOperator.CompletedNativeCentralProductDressingAudit

namespace CarryCriticalTfvd
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl NativeLaguerre
open Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

abbrev h (n : ℕ) : ℝ := canonicalCompletedNativeLogDerivativeMoment n

/-- A readout of the original response, after the complete vector source.
This does not redefine any moment, amplitude or physical state. -/
def responseReadout (t : ℂ) : ℂ := -Complex.I * completedGreenNormalizedResponse
  completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion (Complex.I*t)

def responseCoefficient (n : ℕ) : ℂ :=
  -Complex.I*Complex.I^n*completedNativeGreenResponseTaylorCoefficient n

theorem response_readout_analytic : AnalyticAt ℂ responseReadout 0 := by
  have hh := completedNativeGreenNormalizedResponse_analyticAt.fun_comp_of_eq
    (show AnalyticAt ℂ (fun t : ℂ => Complex.I*t) 0 by fun_prop) (by simp)
  exact analyticAt_const.mul hh

theorem response_coefficient_derivative (n : ℕ) :
    iteratedDeriv n responseReadout 0/(n.factorial : ℂ)=responseCoefficient n := by
  unfold responseReadout responseCoefficient completedNativeGreenResponseTaylorCoefficient
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_mul_zero]
  ring

theorem response_coefficient_even (j : ℕ) : responseCoefficient (2*j)=0 := by
  simp [responseCoefficient, completedNativeGreenResponseTaylorCoefficient_even_eq_zero]

theorem response_coefficient_odd (j : ℕ) :
    responseCoefficient (2*j+1)=(-1 : ℂ)^j*(h j : ℂ) := by
  rw [responseCoefficient, completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  rw [pow_add, show Complex.I^(2*j)=(-1 : ℂ)^j by rw [pow_mul, Complex.I_sq]]
  ring_nf
  norm_num [Complex.I_sq]

/-- Reuse of the old source Taylor law, only through the order required for
the new PR93 sector split. No sign of any coefficient is received. -/
theorem response_seventh_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ t : ℂ in nhds 0,
      responseReadout t=(h 0 : ℂ)*t-(h 1 : ℂ)*t^3+(h 2 : ℂ)*t^5+t^7*R t := by
  obtain ⟨R,hR,he⟩ := response_readout_analytic.exists_eventuallyEq_sum_add_pow_mul 7
  refine ⟨R,hR,?_⟩
  filter_upwards [he] with t ht
  rw [ht]
  have hp : (∑ n ∈ Finset.range 7, (t^n/(n.factorial : ℂ)) • iteratedDeriv n responseReadout 0)=
      ∑ n ∈ Finset.range 7, responseCoefficient n*t^n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [← response_coefficient_derivative]
    simp only [smul_eq_mul]
    ring
  rw [hp]
  have c0 := response_coefficient_even 0
  have c1 := response_coefficient_odd 0
  have c2 := response_coefficient_even 1
  have c3 := response_coefficient_odd 1
  have c4 := response_coefficient_even 2
  have c5 := response_coefficient_odd 2
  have c6 := response_coefficient_even 3
  norm_num only at c0 c1 c2 c3 c4 c5 c6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0,c1,c2,c3,c4,c5,c6,smul_eq_mul]
  ring

def radialStep (k : ℕ) : ℝ := ((k : ℝ)+1)⁻¹
def monomialWeight (p j : ℕ) : ℂ := ((j+1 : ℕ) : ℂ)^p
def remainderWeight (R : ℂ → ℂ) (t : ℝ) (j : ℕ) : ℂ :=
  ((j+1 : ℕ) : ℂ)^7 * R (((j+1 : ℕ) : ℂ)*(t : ℂ))

theorem radial_step_tendsto : Tendsto radialStep atTop (nhds 0) := by
  change Tendsto (fun k : ℕ => ((k : ℝ)+1)⁻¹) atTop (nhds 0)
  have hh := Complex.continuous_re.continuousAt.tendsto.comp canonicalGreenJetStep_tendsto_zero
  simpa [radialStep,Function.comp_def,canonicalGreenJetStep,← Complex.ofReal_natCast,
    ← Complex.ofReal_one,← Complex.ofReal_add,← Complex.ofReal_inv] using hh

theorem response_radial_readout (k j : ℕ) :
    responseWeight k j=Complex.I*responseReadout (((j+1 : ℕ) : ℂ)*(radialStep k : ℂ)) := by
  have hp : canonicalCompletedC3RadialTiltPoint k j=
      Complex.I*(((j+1 : ℕ) : ℂ)*(radialStep k : ℂ)) := by
    unfold canonicalCompletedC3RadialTiltPoint canonicalCompletedC3RadialTiltStep canonicalGreenJetStep radialStep
    push_cast
    ring
  unfold responseWeight responseReadout
  rw [hp]
  ring_nf
  norm_num [Complex.I_sq]

theorem response_weight_taylor :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop, ∀ j : Fin 4,
      responseWeight k j=Complex.I*((h 0 : ℂ)*(radialStep k : ℂ)*monomialWeight 1 j-
        (h 1 : ℂ)*(radialStep k : ℂ)^3*monomialWeight 3 j+
        (h 2 : ℂ)*(radialStep k : ℂ)^5*monomialWeight 5 j+
        (radialStep k : ℂ)^7*remainderWeight R (radialStep k) j) := by
  obtain ⟨R,hR,he⟩ := response_seventh_remainder
  refine ⟨R,hR,?_⟩
  have ht (j : Fin 4) : Tendsto (fun k : ℕ => ((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))
      atTop (nhds 0) := by
    have hv := Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_tendsto
    simpa only [Function.comp_def, Complex.ofReal_zero, mul_zero] using hv.const_mul (((j.val+1 : ℕ) : ℂ))
  have hall : ∀ᶠ k : ℕ in atTop, ∀ j : Fin 4,
      responseReadout (((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ)) =
        (h 0 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))-
        (h 1 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^3+
        (h 2 : ℂ)*(((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^5+
        (((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ))^7*R (((j.val+1 : ℕ) : ℂ)*(radialStep k : ℂ)) := by
    rw [eventually_all]
    exact fun j => (ht j).eventually he
  filter_upwards [hall] with k hk
  intro j
  rw [response_radial_readout, hk j]
  unfold monomialWeight remainderWeight
  ring

end
end CarryCriticalTfvd
