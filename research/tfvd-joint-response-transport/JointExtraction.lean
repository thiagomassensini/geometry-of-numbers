import JointNumerator

namespace CarryTfvdJoint
open CarrySelfAdjointOperator PhysicalSewing CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Regularity comes from the actual material derivative, with its exact log tail. -/
theorem value_hasDerivAt_zero (M : ℕ) :
    HasDerivAt (value M) (-logJet M 0 * Complex.I) 0 := by
  have hs : operatorHeightParameter 0 ∈ genuineCriticalStrip :=
    zero_mem_completedNativeHeightDomain
  have hp : operatorHeightParameter 0 ∈ bracketHalfPlane := by
    change -1 < (operatorHeightParameter 0).re
    linarith [hs.1]
  have hd := (hasDerivAt_canonicalCompletedC3EnrichedTfvdValueTailReadout hp).comp
    0 (hasDerivAt_operatorHeightParameter 0)
  have heq : value M =ᶠ[nhds (0 : ℂ)]
      (fun z => canonicalCompletedC3EnrichedTfvdValueTailReadout (operatorHeightParameter z)) := by
    filter_upwards [isOpen_completedNativeHeightDomain.mem_nhds
      zero_mem_completedNativeHeightDomain] with z hz
    apply canonicalC3BracketTfvdCompletionState_valueReadout_eq_completed
    change -1 < (operatorHeightParameter z).re
    linarith [hz.1]
  have hL := canonicalC3BracketTfvdCompletionState_logJetReadout_eq_completed M hp
  unfold logJet
  rw [hL]
  exact hd.congr_of_eventuallyEq heq

/-- The complete material value is nonzero at the original center. -/
theorem value_zero_ne (M : ℕ) : value M 0 ≠ 0 :=
  (tfvdCanonicalResponse_regular_denominators M 0 zero_mem_completedNativeHeightDomain
    completedNativeOperatorCharacteristic_zero_ne_zero).2.2

/-- Central cancellation belongs to the complete source, not a fitted head. -/
theorem full_response_zero : originalResponse 0 = 0 :=
  completedNativeLogDerivativeHerglotzCoordinate_zero

/-- A source germ identity; no assumption about the sign of any moment. -/
theorem centered_numerator_eventuallyEq (M : ℕ) :
    (fun z => numerator M 0 z) =ᶠ[nhds (0 : ℂ)]
      (fun z => value M 0 * value M z * originalResponse z) := by
  have hF := completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
    completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [isOpen_completedNativeHeightDomain.mem_nhds
    zero_mem_completedNativeHeightDomain,hF] with z hz hFz
  rw [numerator_eq_full_difference M 0 z zero_mem_completedNativeHeightDomain hz
    completedNativeOperatorCharacteristic_zero_ne_zero hFz,full_response_zero,sub_zero]

/-- First jointly surviving coefficient of the complete TFVD producer.
The material derivative term cancels because the WHOLE response vanishes at zero. -/
theorem centered_numerator_hasDerivAt (M : ℕ) :
    HasDerivAt (fun z => numerator M 0 z)
      (2 * value M 0 ^ 2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) 0 := by
  have ha : HasDerivAt originalResponse
      (2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) 0 :=
    hasDerivAt_completedNativeLogDerivativeHerglotzCoordinate_zero
  have ht := ((hasDerivAt_const (0 : ℂ) (value M 0)).mul
    (value_hasDerivAt_zero M)).mul ha
  have ht' : HasDerivAt (fun z => value M 0 * value M z * originalResponse z)
      (2 * value M 0 ^ 2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) 0 := by
    apply ht.congr_deriv
    simp only [Pi.mul_apply,full_response_zero,mul_zero,zero_mul,zero_add]
    ring
  exact ht'.congr_of_eventuallyEq (centered_numerator_eventuallyEq M)

/-- The confluence is the actual derivative, not the zero fallback of a quotient. -/
theorem centered_numerator_coefficient (M : ℕ) :
    dslope (fun z => numerator M 0 z) 0 0 / (value M 0 ^ 2) =
      2 * (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  rw [dslope_same,(centered_numerator_hasDerivAt M).deriv]
  field_simp [value_zero_ne M]

/-- The complete two-point numerator has the same first coefficient at any exact cutoff. -/
theorem centered_numerator_coefficient_cutoff (M N : ℕ) :
    deriv (fun z => numerator M 0 z) 0 = deriv (fun z => numerator N 0 z) 0 := by
  rw [(centered_numerator_hasDerivAt M).deriv,(centered_numerator_hasDerivAt N).deriv,
    (readouts_cutoff_independent M N 0 zero_mem_completedNativeHeightDomain).1]


/-- Divide only after the complete joint numerator has been assembled.
This scalar germ is a readout, not a newly defined Hilbert state. -/
def normalizedCenteredNumerator (M : ℕ) (z : ℂ) : ℂ :=
  numerator M 0 z / (value M 0 * value M z)

theorem normalizedCenteredNumerator_eventuallyEq (M : ℕ) :
    normalizedCenteredNumerator M =ᶠ[nhds (0 : ℂ)] originalResponse := by
  have hn := (value_hasDerivAt_zero M).continuousAt.eventually_ne (value_zero_ne M)
  filter_upwards [centered_numerator_eventuallyEq M,hn] with z hz hnz
  unfold normalizedCenteredNumerator
  rw [hz]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (value_zero_ne M) hnz)

/-- All jets are extracted from the SAME joint TFVD numerator.
This is exact coefficient provenance; it does not prove their signs. -/
theorem normalizedCenteredNumerator_odd_coefficient (M n : ℕ) :
    iteratedDeriv (2*n+1) (normalizedCenteredNumerator M) 0 /
      ((2*n+1).factorial : ℂ) =
      2 * (canonicalCompletedNativeLogDerivativeMoment n : ℂ) := by
  rw [(normalizedCenteredNumerator_eventuallyEq M).iteratedDeriv_eq (2*n+1)]
  have hf : originalResponse = fun z => 2 *
      completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion z := by
    funext z
    unfold originalResponse completedGreenNormalizedResponse
    rw [completedNativeOperatorBoundaryCompanion_eq_neg_deriv]
    ring
  rw [hf,iteratedDeriv_const_mul_field]
  have hc := completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical n
  unfold completedNativeGreenResponseTaylorCoefficient at hc
  rw [mul_div_assoc,hc]

end
end CarryTfvdJoint
