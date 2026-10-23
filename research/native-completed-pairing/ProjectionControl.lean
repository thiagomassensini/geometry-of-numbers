import SignedFrontier

/-! A controlled test AFTER the complete source identity. The normalized
SCALAR TRACE PROJECTION is tested as a Gram feature family in its existing
boundary carrier. It is not substituted for the enriched physical state.
Its exact defect does not constitute a no-go for that full state. -/
namespace CarryCompletedPairing
open CarryCameraTail CarryMaterialTheta CarryFourLeg CarryGreenProvenance
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open Filter
open scoped ComplexConjugate Topology
noncomputable section
set_option autoImplicit false

def normalizedScalarTrace (M : ℕ) (z : ℂ) : CompletedScalarBoundaryTraceCarrier :=
  (((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic z)⁻¹ •
    WithLp.toLp 2 ((completedIntegralTrace (M+1) z).2, (completedIntegralTrace (M+1) z).1)

theorem normalized_scalar_trace_germ (M : ℕ) :
    ∀ᶠ z in nhds (0 : ℂ),
      (normalizedScalarTrace M z).fst =
        (2 / ((Real.sqrt 2 : ℝ) : ℂ)) *
          completedGreenNormalizedResponse completedNativeOperatorCharacteristic
            completedNativeOperatorBoundaryCompanion z ∧
      (normalizedScalarTrace M z).snd = (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
  have hd : completedNativeHeightDomain ∈ nhds (0 : ℂ) :=
    isOpen_completedNativeHeightDomain.mem_nhds zero_mem_completedNativeHeightDomain
  have hn : ∀ᶠ z in nhds (0 : ℂ), completedNativeOperatorCharacteristic z ≠ 0 :=
    completedNativeOperatorCharacteristic_differentiableAt_zero.continuousAt.eventually_ne
      completedNativeOperatorCharacteristic_zero_ne_zero
  filter_upwards [hd,hn] with z hz hF
  unfold normalizedScalarTrace
  rw [completed_trace_mellin (M+1) z hz.1,
    canonicalC3BracketTfvdCompletedTracePair_eq_F_negFprime (M+1) hz]
  change
    (((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic z)⁻¹ *
      (-deriv completedNativeOperatorCharacteristic z) = _ ∧
    (((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic z)⁻¹ *
      completedNativeOperatorCharacteristic z = _
  have hroot : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  constructor
  · change _ = (2 / ((Real.sqrt 2 : ℝ) : ℂ)) *
      (-deriv completedNativeOperatorCharacteristic z / (2 * completedNativeOperatorCharacteristic z))
    field_simp
  · field_simp

/-- Coordinatewise Taylor coefficient of the existing finite boundary
carrier. It is derived solely from normalizedScalarTrace, never from h. -/
def projectedEvenJet (M n : ℕ) : CompletedScalarBoundaryTraceCarrier :=
  WithLp.toLp 2
    (iteratedDeriv (2*n) (fun z => (normalizedScalarTrace M z).fst) 0 / ((2*n).factorial : ℂ),
     iteratedDeriv (2*n) (fun z => (normalizedScalarTrace M z).snd) 0 / ((2*n).factorial : ℂ))

theorem projected_even_jet_exact (M n : ℕ) :
    projectedEvenJet M n =
      if n = 0 then WithLp.toLp 2 (0, (((Real.sqrt 2 : ℝ) : ℂ))⁻¹)
      else 0 := by
  have hf : (fun z => (normalizedScalarTrace M z).fst) =ᶠ[nhds (0 : ℂ)]
      (fun z => (2 / ((Real.sqrt 2 : ℝ) : ℂ)) *
        completedGreenNormalizedResponse completedNativeOperatorCharacteristic
          completedNativeOperatorBoundaryCompanion z) := by
    filter_upwards [normalized_scalar_trace_germ M] with z hz
    exact hz.1
  have hv : (fun z => (normalizedScalarTrace M z).snd) =ᶠ[nhds (0 : ℂ)]
      (fun _ => (((Real.sqrt 2 : ℝ) : ℂ))⁻¹) := by
    filter_upwards [normalized_scalar_trace_germ M] with z hz
    exact hz.2
  unfold projectedEvenJet
  rw [hf.iteratedDeriv_eq (2*n), hv.iteratedDeriv_eq (2*n), iteratedDeriv_const_mul_field]
  have hc := completedNativeGreenResponseTaylorCoefficient_even_eq_zero n
  change iteratedDeriv (2*n)
    (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion) 0 / ((2*n).factorial : ℂ) = 0 at hc
  rw [mul_div_assoc, hc, mul_zero, iteratedDeriv_const]
  by_cases hn : n = 0
  · subst n
    simp
  · have hdegree : 2*n ≠ 0 := by omega
    simp [hn, hdegree]

theorem projected_even_gram_00 (M : ℕ) :
    inner ℂ (projectedEvenJet M 0) (projectedEvenJet M 0) = (1/2 : ℂ) := by
  rw [projected_even_jet_exact]
  simp only [if_true, WithLp.prod_inner_apply, RCLike.inner_apply']
  change conj (0 : ℂ)*0 +
    conj ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = _
  simp only [map_zero, zero_mul, zero_add, map_inv₀, Complex.conj_ofReal]
  have hr : (((Real.sqrt 2 : ℝ) : ℂ))^2 = (2 : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  rw [← mul_inv, ← pow_two, hr]
  norm_num

theorem projected_even_gram_01 (M : ℕ) :
    inner ℂ (projectedEvenJet M 0) (projectedEvenJet M 1) = 0 := by
  rw [projected_even_jet_exact M 1]
  norm_num

theorem projected_even_gram_11 (M : ℕ) :
    inner ℂ (projectedEvenJet M 1) (projectedEvenJet M 1) = 0 := by
  rw [projected_even_jet_exact M 1]
  norm_num

/-- Exact defects for the requested three even-sector entries. This tests
the projected trace shortcut, not the full enriched physical carrier. -/
theorem projected_gram_three_defects (M : ℕ) :
    (inner ℂ (projectedEvenJet M 0) (projectedEvenJet M 0) -
       (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ),
     inner ℂ (projectedEvenJet M 0) (projectedEvenJet M 1) -
       (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ),
     inner ℂ (projectedEvenJet M 1) (projectedEvenJet M 1) -
       (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ)) =
      ((1/2 : ℂ) - canonicalCompletedNativeLogDerivativeMoment 0,
       -(canonicalCompletedNativeLogDerivativeMoment 1 : ℂ),
       -(canonicalCompletedNativeLogDerivativeMoment 2 : ℂ)) := by
  rw [projected_even_gram_00, projected_even_gram_01, projected_even_gram_11]
  simp

end
end CarryCompletedPairing
