import GeometryOfNumbers.Analysis.CarryMaterialCentralProjectionBounds
import CarrySelfAdjointOperator.CompletedNativeChiralReturnSeventhSourceJet
import GeometryOfNumbers.Analysis.CarryMaterialResidualResponse
import CarrySelfAdjointOperator.NativeCompletedSourceTwoPositiveChannels
import GeometryOfNumbers.Analysis.CarryMaterialNormalizedResponse
import CarrySelfAdjointOperator.NativeCompletedSourcePositiveReductionJet
import Mathlib.Analysis.Complex.RealDeriv
import GeometryOfNumbers.Analysis.CarryMaterialCentralCalibration
import CarrySelfAdjointOperator.C2GeometryNativeSourceBridge
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
import CarrySelfAdjointOperator.CompletedNativeAmbientCentralCurvatureDecision
import Lean

/-! Read-only cross-repository verification with identical Lean/Mathlib and
GreenFrame pins. This file is deliberately outside the default library: it
does not add a dependency or change either manifest. -/
namespace CarryMaterialCanonicalComparison
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator NativeCarrySpectralWeyl.Camera
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem height_parameter (t : ℝ) :
    baseTwoDressingParameter (t : ℂ) = operatorHeightParameter (t : ℂ) := rfl

theorem native_line_parameter (t : ℝ) :
    nativeLine t = operatorHeightParameter (t : ℂ) := by
  simp only [nativeLine, operatorHeightParameter, mul_comm Complex.I]

theorem material_sample (t : ℝ) (n : ℕ) (hn : 0 < n) :
    criticalMaterialSample t n = dirichletValue (nativeLine t) n := by
  rw [criticalMaterialSample_eq_cpow t hn]
  unfold dirichletValue
  congr 1
  simp only [criticalMaterialExponent, nativeLine]
  ring

theorem material_cell (t : ℝ) (k : ℕ) :
    baseTwoCriticalCenterCell t k = centerBracketTerm 2 (nativeLine t) k := by
  simp only [baseTwoCriticalCenterCell, baseTwo_leftLeg_eq, baseTwo_center_eq,
    baseTwo_rightLeg_eq, centerBracketTerm, if_true, centeredBracketTerm,
    FiniteNativeCarryOperator.Camera.alignedCenter_two]
  rw [material_sample t _ (by omega), material_sample t _ (by omega),
    material_sample t _ (by omega)]

theorem material_signal (t : ℝ) :
    baseTwoCriticalCompleteSignal t = bracketCharacteristic 2 (nativeLine t) := by
  simp only [baseTwoCriticalCompleteSignal, bracketCharacteristic, seedDirichletTerm,
    if_true, material_sample t 1 (by decide), material_cell]

/-- The gradient component is literally the ordinary C3 gradient on the same
native line. This identifies a component, not the full ambient/material state. -/
theorem material_gradient (t : ℝ)
    (ht : 0 < (operatorHeightParameter (t : ℂ)).re) :
    baseTwoCompletedMaterialGradientL2 t =
      canonicalCompletedC3DirichletGradientState (operatorHeightParameter (t : ℂ)) ht := by
  apply lp.ext
  funext n
  simp only [baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply,
    canonicalCompletedC3DirichletGradientState_apply,
    criticalMaterialGradient_eq_nativeLinePowerDifference,
    CPFormal.Analytic.Cp.positiveDirichletGradient, CPFormal.Analytic.Cp.natDirichletTerm,
    CPFormal.Analytic.Cp.dirichletTerm, Int.cast_natCast, height_parameter]

theorem material_camera_factor (t : ℝ) :
    baseTwoCanonicalCameraFactor t = factor 2 (nativeLine t) := by
  simp only [baseTwoCanonicalCameraFactor, baseTwoCanonicalCameraFactorComplex,
    factor_two, c2Factor, baseTwoDressingParameter, nativeLine, mul_comm Complex.I]

theorem material_completion_factor (t : ℝ) :
    canonicalArchimedeanCompletion t = nativeXiCompletionFactor (t : ℂ) := rfl

/-- Exact scalar identification for the whole synthesized source, at every
real time, with the parameter map proved above. No vector Gram is inferred. -/
theorem material_response (t : ℝ) :
    baseTwoCanonicalResponse t = completedNativeOperatorCharacteristic (t : ℂ) := by
  have hd : nativeLine t ∈ nativeScalarDomain := by
    simp [nativeScalarDomain, nativeLine_re]
    norm_num
  rw [baseTwoCanonicalResponse, material_completion_factor, material_signal,
    bracketCharacteristic_eq_factor_mul_nativeScalar (by decide) hd, material_camera_factor]
  have hf : factor 2 (nativeLine t) ≠ 0 := by
    rw [← material_camera_factor]
    exact baseTwoCanonicalCameraFactor_ne_zero t
  have hc : factor 2 (nativeLine t) * nativeScalar (nativeLine t) *
      (factor 2 (nativeLine t))⁻¹ = nativeScalar (nativeLine t) := by
    field_simp [hf]
  rw [hc, native_line_parameter]
  rfl

theorem material_canonical_central_mass_gt_quarter :
    (1 / 4 : ℝ) <
      ‖(((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic 0)⁻¹ •
        baseTwoVectorDressing 0 (baseTwoCompletedBoundaryHilbertState 0)‖ ^ 2 := by
  simpa only [material_response, Complex.ofReal_zero] using carryMaterial_origin_normalized_mass_gt_quarter

/-- The literal dressed-source candidate fails central calibration with the
actual native moment, with a fixed gap. This refutes only this candidate. -/
theorem material_canonical_central_defect_gt_three_sixteenths :
    (3 / 16 : ℝ) <
      ‖(((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic 0)⁻¹ •
        baseTwoVectorDressing 0 (baseTwoCompletedBoundaryHilbertState 0)‖ ^ 2 -
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hm := material_canonical_central_mass_gt_quarter
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  linarith

theorem material_canonical_central_defect_exact :
    ‖(((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic 0)⁻¹ •
        baseTwoVectorDressing 0 (baseTwoCompletedBoundaryHilbertState 0)‖ ^ 2 -
        canonicalCompletedNativeLogDerivativeMoment 0 =
      (1 / 4 - canonicalCompletedNativeLogDerivativeMoment 0) +
        (2 * ‖baseTwoCompletedMaterialGradientL2 0‖ ^ 2 +
          ‖1 - baseTwoCompletedBoundaryValue 0‖ ^ 2) / (4 * ‖baseTwoCriticalCompleteSignal 0‖ ^ 2) := by
  simpa only [material_response, Complex.ofReal_zero] using
    carryMaterial_origin_normalized_defect (canonicalCompletedNativeLogDerivativeMoment 0)

theorem material_canonical_central_defect_physical :
    ‖(((Real.sqrt 2 : ℝ) : ℂ) * completedNativeOperatorCharacteristic 0)⁻¹ •
        baseTwoVectorDressing 0 (baseTwoCompletedBoundaryHilbertState 0)‖ ^ 2 -
        canonicalCompletedNativeLogDerivativeMoment 0 =
      (1 / 4 - canonicalCompletedNativeLogDerivativeMoment 0) +
        (2 * ‖baseTwoPhysicalOrdinaryC2State 0‖ ^ 2 +
          2 * ‖baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 0)‖ ^ 2 +
          ‖1 - baseTwoCompletedBoundaryValue 0‖ ^ 2) / (4 * ‖baseTwoCriticalCompleteSignal 0‖ ^ 2) := by
  simpa only [material_response, Complex.ofReal_zero] using
    carryMaterial_origin_normalized_defect_physical (canonicalCompletedNativeLogDerivativeMoment 0)

theorem canonical_kernel_at_origin :
    dslope (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion) 0 0 =
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simp only [dslope_same, completedNativeGreenNormalizedResponse_hasDerivAt_h0.deriv]

/-- At ORDER zero, the factorial-normalized jet is the value. This fact
does not supply holomorphy or any higher-order jet identification. -/
theorem normalized_jet_order_zero
    (state : ℂ → BaseTwoCompletedBoundaryHilbertCarrier) :
    completedGreenTaylorJet (normalizedCompletedGreenState completedNativeOperatorCharacteristic state) 0 =
      normalizedCompletedGreenState completedNativeOperatorCharacteristic state 0 := by
  simp [completedGreenTaylorJet]

/-- The earlier negative curvature defect is minus a positive characteristic
weight times its normalized Gram gap. The two sign conventions agree. -/
theorem ambient_curvature_defect_eq_negative_normalized_gap :
    canonicalCompletedAmbientCentralCurvatureDefect =
      -4 * ‖completedNativeOperatorCharacteristic 0‖ ^ 2 *
        (‖canonicalCompletedC3NormalizedAmbientResponseState 0
          (by norm_num [operatorHeightParameter])‖ ^ 2 -
          canonicalCompletedNativeLogDerivativeMoment 0) := by
  rw [canonicalCompletedAmbientCentralCurvatureDefect_eq_characteristicWeightedMoment_sub_gradient,
    norm_sq_canonicalCompletedC3NormalizedAmbientResponseState_zero]
  have hf : ‖completedNativeOperatorCharacteristic 0‖ ≠ 0 :=
    norm_ne_zero_iff.mpr completedNativeOperatorCharacteristic_zero_ne_zero
  field_simp
  ring

/-- Even just the literal candidate's value at zero excludes the normalized
Green contract. No differentiability or holomorphic extension is assumed. -/
theorem no_normalized_kernel_with_literal_material_origin
    (state : ℂ → BaseTwoCompletedBoundaryHilbertCarrier)
    (hzero : state 0 = baseTwoVectorDressing 0 (baseTwoCompletedBoundaryHilbertState 0)) :
    ¬ HasCompletedNativeRealAxisNormalizedGreenKernel state := by
  intro hk
  have hd := hk 0 0 completedNativeOperatorCharacteristic_zero_ne_zero
    completedNativeOperatorCharacteristic_zero_ne_zero
  simp only [Complex.ofReal_zero, dslope_same,
    completedNativeGreenNormalizedResponse_hasDerivAt_h0.deriv] at hd
  rw [normalizedCompletedGreenState, hzero, inner_self_eq_norm_sq_to_K] at hd
  have hreal := congrArg (RCLike.re : ℂ → ℝ) hd
  simp only [← RCLike.ofReal_pow, RCLike.ofReal_re] at hreal
  change _ = canonicalCompletedNativeLogDerivativeMoment 0 at hreal
  have hm := material_canonical_central_mass_gt_quarter
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_lt_sixteenth
  nlinarith

end
end CarryMaterialCanonicalComparison

-- Transitive type-and-body audit, independent of the default library guard.
open Lean Elab Command
elab "#assert_central_comparison_axioms " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← collectAxioms decl
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "Central comparison unexpected axiom: {decl} depends on {axiomName}"

namespace CarryMaterialCanonicalComparison
#assert_central_comparison_axioms height_parameter
#print axioms height_parameter
#assert_central_comparison_axioms native_line_parameter
#print axioms native_line_parameter
#assert_central_comparison_axioms material_sample
#print axioms material_sample
#assert_central_comparison_axioms material_cell
#print axioms material_cell
#assert_central_comparison_axioms material_signal
#print axioms material_signal
#assert_central_comparison_axioms material_gradient
#print axioms material_gradient
#assert_central_comparison_axioms material_camera_factor
#print axioms material_camera_factor
#assert_central_comparison_axioms material_completion_factor
#print axioms material_completion_factor
#assert_central_comparison_axioms material_response
#print axioms material_response
#assert_central_comparison_axioms material_canonical_central_mass_gt_quarter
#print axioms material_canonical_central_mass_gt_quarter
#assert_central_comparison_axioms material_canonical_central_defect_gt_three_sixteenths
#print axioms material_canonical_central_defect_gt_three_sixteenths
#assert_central_comparison_axioms material_canonical_central_defect_exact
#print axioms material_canonical_central_defect_exact
#assert_central_comparison_axioms material_canonical_central_defect_physical
#print axioms material_canonical_central_defect_physical
#assert_central_comparison_axioms canonical_kernel_at_origin
#print axioms canonical_kernel_at_origin
#assert_central_comparison_axioms normalized_jet_order_zero
#print axioms normalized_jet_order_zero
#assert_central_comparison_axioms ambient_curvature_defect_eq_negative_normalized_gap
#print axioms ambient_curvature_defect_eq_negative_normalized_gap
#assert_central_comparison_axioms no_normalized_kernel_with_literal_material_origin
#print axioms no_normalized_kernel_with_literal_material_origin
end CarryMaterialCanonicalComparison

namespace CarryMaterialResponseComparison
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator CarryMaterialCanonicalComparison
open CarrySelfAdjointOperator.SourcePositiveReduction
open Filter
open scoped Topology InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Derivatives are transported by restricting the known holomorphic SCALAR
characteristic to the real axis. No holomorphy of the material state is used. -/
theorem material_characteristic_hasDerivAt (t : ℝ) :
    HasDerivAt baseTwoCanonicalResponse
      (deriv completedNativeOperatorCharacteristic (t : ℂ)) t := by
  have he : baseTwoCanonicalResponse =
      fun u : ℝ => completedNativeOperatorCharacteristic (u : ℂ) := funext material_response
  rw [he]
  exact (completedNativeOperatorCharacteristic_analyticAt
    (ofReal_mem_completedNativeHeightDomain t)).differentiableAt.hasDerivAt.comp_ofReal

theorem material_companion (t : ℝ) :
    baseTwoCompletedBoundaryHilbertReadout (carryMaterialDressedCompanion t
      ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩) =
      completedNativeOperatorBoundaryCompanion (t : ℂ) := by
  rw [carryMaterialDressedCompanion_source_readout, (material_characteristic_hasDerivAt t).deriv]
  rfl

/-- The original scalar Green pair comes from the full vector companion,
including the derivative of the dressing and the clocked global return. -/
theorem material_boundary_pair (t : ℝ) :
    (baseTwoCompletedBoundaryHilbertReadout (carryMaterialDressedCompanion t
        ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩),
      baseTwoCompletedBoundaryHilbertReadout (baseTwoVectorDressing t
        (baseTwoCompletedBoundaryHilbertState t))) =
      canonicalCompletedC3ScalarBoundaryPair (t : ℂ) := by
  rw [material_companion, carryMaterial_dressed_completed_readout, material_response]
  rfl

theorem material_normalized_response (t : ℝ) :
    carryMaterialNormalizedResponse t =
      completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion (t : ℂ) := by
  rw [carryMaterialNormalizedResponse, carryMaterialResponseReadout,
    material_companion, carryMaterial_dressed_completed_readout, material_response]
  rfl

theorem material_normalized_response_zero : carryMaterialNormalizedResponse 0 = 0 := by
  rw [material_normalized_response]
  simpa only [Complex.ofReal_zero] using completedNativeGreenNormalizedResponse_zero

theorem material_normalized_response_hasDerivAt_zero :
    HasDerivAt carryMaterialNormalizedResponse
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) 0 := by
  have he : carryMaterialNormalizedResponse =
      fun t : ℝ => completedGreenNormalizedResponse completedNativeOperatorCharacteristic
        completedNativeOperatorBoundaryCompanion (t : ℂ) := funext material_normalized_response
  rw [he]
  exact completedNativeGreenNormalizedResponse_hasDerivAt_h0.comp_ofReal

/-- Equality of source responses is local; no global vector identification
with the four-sector carrier is asserted. -/
theorem material_source_response_eventually_eq :
    carryMaterialNormalizedResponse =ᶠ[nhds 0] fun t : ℝ => sourceResponse (t : ℂ) := by
  have hc := sourceResponse_eventuallyEq_native
  have hr := hc.comp_tendsto (show Tendsto (fun t : ℝ => (t : ℂ)) (nhds 0) (nhds 0) from
    by simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto 0)
  filter_upwards [hr] with t ht
  exact (material_normalized_response t).trans ht.symm

theorem material_axis_zero :
    carryMaterialResponseAxis 0 = (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
  simpa only [carryMaterialResponseAxis, dslope_same] using material_normalized_response_hasDerivAt_zero.deriv

theorem material_axis_eventually_eq :
    carryMaterialResponseAxis =ᶠ[nhds 0] fun t : ℝ => sourceAxis (t : ℂ) := by
  filter_upwards [material_source_response_eventually_eq] with t ht
  by_cases hz : t = 0
  · subst t
    simpa only [Complex.ofReal_zero, sourceAxis_zero] using material_axis_zero
  · have hc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
    have he := sourceResponse_eq_mul_axis (t : ℂ)
    rw [← ht] at he
    rw [carryMaterialResponseAxis, dslope_of_ne _ hz]
    simp only [slope, sub_zero, material_normalized_response_zero]
    rw [he]
    simp [Complex.real_smul, hc]

theorem material_scale_eq : carryMaterialResponseScale = canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [carryMaterialResponseScale, material_axis_zero, Complex.ofReal_re]

theorem material_scale_pos : 0 < carryMaterialResponseScale := by
  rw [material_scale_eq]
  exact canonicalCompletedNativeLogDerivativeMoment_zero_pos

theorem material_feature_eventually_eq :
    carryMaterialPositiveFeature =ᶠ[nhds 0] fun t : ℝ => positiveFeature (t : ℂ) := by
  filter_upwards [material_axis_eventually_eq] with t ht
  simp only [carryMaterialPositiveFeature, positiveFeature, ht, material_scale_eq, sourceScale_eq]

theorem material_feature_center_energy :
    ‖carryMaterialPositiveFeature 0‖ ^ 2 = canonicalCompletedNativeLogDerivativeMoment 0 := by
  have he := material_feature_eventually_eq.eq_of_nhds
  rw [he]
  simpa only [Complex.ofReal_zero, sourceScale_eq] using positiveFeature_center_energy

theorem material_feature_center_row :
    ∀ᶠ t : ℝ in nhds 0,
      inner ℂ (carryMaterialPositiveFeature 0) (carryMaterialPositiveFeature t) =
        carryMaterialResponseAxis t := by
  have hz := material_feature_eventually_eq.eq_of_nhds
  filter_upwards [material_feature_eventually_eq, material_axis_eventually_eq] with t ht ha
  rw [hz, ht, Complex.ofReal_zero, positiveFeature_center_row, ha]

/-- A genuine two-input identity for the extracted channel, not the full
material Hilbert Gram. -/
theorem material_feature_pairing_local :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U,
        inner ℂ (carryMaterialPositiveFeature t) (carryMaterialPositiveFeature u) =
          inner ℂ (positiveFeature (t : ℂ)) (positiveFeature (u : ℂ)) := by
  rcases mem_nhds_iff.mp material_feature_eventually_eq with ⟨U, hU, ho, hz⟩
  refine ⟨U, ho, hz, ?_⟩
  intro t ht u hu
  rw [hU ht, hU hu]

/-- The complete source numerator, with both independent real parameters.
There is no division by their difference, including at a collision. -/
theorem material_kernel_numerator_split_local :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U,
        carryMaterialNormalizedResponse u - conj (carryMaterialNormalizedResponse t) =
          ((u : ℂ) - conj (t : ℂ)) *
            inner ℂ (carryMaterialPositiveFeature t) (carryMaterialPositiveFeature u) +
          conj (carryMaterialNormalizedResponse t) * carryMaterialNormalizedResponse u *
            (reducedResponse (u : ℂ) - conj (reducedResponse (t : ℂ))) := by
  have hn := (show Tendsto (fun t : ℝ => (t : ℂ)) (nhds 0) (nhds 0) from
      by simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto 0).eventually
        sourceAxis_eventually_ne_zero
  rcases mem_nhds_iff.mp (material_source_response_eventually_eq.and
      (material_feature_eventually_eq.and hn)) with ⟨U, hU, ho, hz⟩
  refine ⟨U, ho, hz, ?_⟩
  intro t ht u hu
  rw [(hU ht).1, (hU hu).1, (hU ht).2.1, (hU hu).2.1]
  exact sourceKernel_numerator_split _ _ (hU ht).2.2 (hU hu).2.2

/-- The divided kernel is used only at separated real parameters. Central
calibration was proved independently above; no 0/0 value is substituted. -/
theorem material_kernel_split_local :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U, u ≠ t →
        (carryMaterialNormalizedResponse u - conj (carryMaterialNormalizedResponse t)) /
            ((u : ℂ) - conj (t : ℂ)) =
          inner ℂ (carryMaterialPositiveFeature t) (carryMaterialPositiveFeature u) +
          conj (carryMaterialNormalizedResponse t) * carryMaterialNormalizedResponse u *
            reducedKernel (t : ℂ) (u : ℂ) := by
  rcases material_kernel_numerator_split_local with ⟨U, ho, hz, hU⟩
  refine ⟨U, ho, hz, ?_⟩
  intro t ht u hu hne
  have hd : (u : ℂ) - conj (t : ℂ) ≠ 0 := by
    simpa only [Complex.conj_ofReal, ne_eq, sub_eq_zero, Complex.ofReal_inj] using hne
  rw [hU t ht u hu, reducedKernel]
  field_simp

end
end CarryMaterialResponseComparison

namespace CarryMaterialResponseComparison
#assert_central_comparison_axioms material_characteristic_hasDerivAt
#print axioms material_characteristic_hasDerivAt
#assert_central_comparison_axioms material_companion
#print axioms material_companion
#assert_central_comparison_axioms material_boundary_pair
#print axioms material_boundary_pair
#assert_central_comparison_axioms material_normalized_response
#print axioms material_normalized_response
#assert_central_comparison_axioms material_normalized_response_zero
#print axioms material_normalized_response_zero
#assert_central_comparison_axioms material_normalized_response_hasDerivAt_zero
#print axioms material_normalized_response_hasDerivAt_zero
#assert_central_comparison_axioms material_source_response_eventually_eq
#print axioms material_source_response_eventually_eq
#assert_central_comparison_axioms material_axis_zero
#print axioms material_axis_zero
#assert_central_comparison_axioms material_axis_eventually_eq
#print axioms material_axis_eventually_eq
#assert_central_comparison_axioms material_scale_eq
#print axioms material_scale_eq
#assert_central_comparison_axioms material_scale_pos
#print axioms material_scale_pos
#assert_central_comparison_axioms material_feature_eventually_eq
#print axioms material_feature_eventually_eq
#assert_central_comparison_axioms material_feature_center_energy
#print axioms material_feature_center_energy
#assert_central_comparison_axioms material_feature_center_row
#print axioms material_feature_center_row
#assert_central_comparison_axioms material_feature_pairing_local
#print axioms material_feature_pairing_local
#assert_central_comparison_axioms material_kernel_numerator_split_local
#print axioms material_kernel_numerator_split_local
#assert_central_comparison_axioms material_kernel_split_local
#print axioms material_kernel_split_local
end CarryMaterialResponseComparison

namespace CarryMaterialResidualComparison
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator.SourcePositiveReduction
open CarrySelfAdjointOperator CarryMaterialResponseComparison
open Filter
open scoped Topology InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem real_cast_tendsto :
    Tendsto (fun t : ℝ => (t : ℂ)) (nhds 0) (nhds 0) := by
  simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto 0

private theorem real_dslope_offdiag (f : ℝ → ℂ) {t u : ℝ} (h : u ≠ t) :
    dslope f t u = (f u-f t)/((u : ℂ)-(t : ℂ)) := by
  rw [dslope_of_ne f h]
  simp [slope, Complex.real_smul, div_eq_mul_inv, mul_comm]

private theorem real_dslope_germ {f : ℝ → ℂ} {g : ℂ → ℂ}
    (he : f =ᶠ[nhds 0] fun t : ℝ => g (t : ℂ))
    (hg : DifferentiableAt ℂ g 0) :
    dslope f 0 =ᶠ[nhds 0] fun t : ℝ => dslope g 0 (t : ℂ) := by
  have hd := hg.hasDerivAt.comp_ofReal.congr_of_eventuallyEq he
  filter_upwards [he] with t ht
  by_cases hz : t = 0
  · subst t
    simpa only [Complex.ofReal_zero, dslope_same] using hd.deriv
  · rw [real_dslope_offdiag f hz, dslope_of_ne g (Complex.ofReal_ne_zero.mpr hz)]
    simp [slope, ht, he.eq_of_nhds, div_eq_mul_inv, mul_comm]

private theorem real_regular_germ {f : ℝ → ℂ} {g : ℂ → ℂ}
    (he : f =ᶠ[nhds 0] fun t : ℝ => g (t : ℂ)) (hg : AnalyticAt ℂ g 0) :
    ∀ᶠ t : ℝ in nhds 0, HasDerivAt f (deriv g (t : ℂ)) t := by
  filter_upwards [real_cast_tendsto.eventually hg.eventually_analyticAt,
    he.eventuallyEq_nhds] with t ht heq
  exact ht.differentiableAt.hasDerivAt.comp_ofReal.congr_of_eventuallyEq heq

theorem material_reduced_eventually_eq :
    carryMaterialReducedResponse =ᶠ[nhds 0] fun t : ℝ => reducedResponse (t : ℂ) := by
  have hd := real_dslope_germ material_axis_eventually_eq
    sourceAxis_analyticAt_zero.differentiableAt
  filter_upwards [hd, material_axis_eventually_eq] with t ht ha
  simp only [carryMaterialReducedResponse, reducedResponse, ht, ha,
    material_scale_eq, sourceScale_eq]

theorem material_reduced_zero : carryMaterialReducedResponse 0 = 0 := by
  have h := material_reduced_eventually_eq.eq_of_nhds
  simpa only [Complex.ofReal_zero, reducedResponse_zero] using h

theorem material_reduced_hasDerivAt_zero :
    HasDerivAt carryMaterialReducedResponse
      ((canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) /
        (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)^2) 0 := by
  simpa only [sourceScale_eq] using
    reducedResponse_hasDerivAt_zero.comp_ofReal.congr_of_eventuallyEq material_reduced_eventually_eq

theorem material_reduced_deriv_real_pos : 0 < (deriv carryMaterialReducedResponse 0).re := by
  rw [material_reduced_hasDerivAt_zero.deriv]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  simpa only [reducedSourceScale_eq, sourceScale_eq] using reducedSourceScale_pos

theorem material_reduced_not_zero_germ :
    ¬ carryMaterialReducedResponse =ᶠ[nhds 0] fun _ => (0 : ℂ) := by
  intro h
  have hd := h.deriv_eq
  have hp := material_reduced_deriv_real_pos
  simp only [deriv_const] at hd
  rw [hd] at hp
  norm_num at hp

theorem material_response_conj (t : ℝ) :
    conj (carryMaterialNormalizedResponse t) = carryMaterialNormalizedResponse t := by
  rw [material_normalized_response, completedNativeGreenNormalizedResponse_ofReal_conj]

theorem material_axis_conj (t : ℝ) :
    conj (carryMaterialResponseAxis t) = carryMaterialResponseAxis t := by
  by_cases ht : t = 0
  · subst t
    rw [material_axis_zero, Complex.conj_ofReal]
  · rw [carryMaterialResponseAxis, real_dslope_offdiag _ ht]
    simp only [map_div₀, map_sub, Complex.conj_ofReal, material_response_conj]

theorem material_reduced_conj (t : ℝ) :
    conj (carryMaterialReducedResponse t) = carryMaterialReducedResponse t := by
  by_cases ht : t = 0
  · subst t
    simp only [material_reduced_zero, map_zero]
  · simp only [carryMaterialReducedResponse, real_dslope_offdiag _ ht,
      map_div₀, map_sub, map_mul, Complex.conj_ofReal, material_axis_conj]

theorem material_weighted_residual_center (t : ℝ) :
    conj (carryMaterialNormalizedResponse 0)*carryMaterialNormalizedResponse t *
      dslope carryMaterialReducedResponse 0 t = 0 := by
  simp only [material_normalized_response_zero, map_zero, zero_mul]

/-- The off-diagonal residual of PR #5 is the divided slope of the actual
reduced MATERIAL response, on one common real neighborhood. -/
theorem material_real_kernel_split_offdiag :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U, u ≠ t →
        dslope carryMaterialNormalizedResponse t u =
          inner ℂ (carryMaterialPositiveFeature t) (carryMaterialPositiveFeature u) +
          conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse u *
            dslope carryMaterialReducedResponse t u := by
  rcases material_kernel_split_local with ⟨V, hV, h0, hsplit⟩
  rcases mem_nhds_iff.mp material_reduced_eventually_eq with ⟨W, hW, ho, hz⟩
  refine ⟨V ∩ W, hV.inter ho, ⟨h0,hz⟩, ?_⟩
  intro t ht u hu hne
  rw [real_dslope_offdiag _ hne, real_dslope_offdiag _ hne]
  have h := hsplit t ht.1 u hu.1 hne
  have htq : carryMaterialReducedResponse t = reducedResponse (t : ℂ) := hW ht.2
  have huq : carryMaterialReducedResponse u = reducedResponse (u : ℂ) := hW hu.2
  rw [reducedKernel, ← htq, ← huq, material_reduced_conj,
    material_response_conj, Complex.conj_ofReal] at h
  simpa only [material_response_conj] using h

/-- Continuity closes every local real diagonal, using the derivatives
already supplied by the same analytic scalar source. -/
theorem material_real_kernel_split :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U,
        dslope carryMaterialNormalizedResponse t u =
          inner ℂ (carryMaterialPositiveFeature t) (carryMaterialPositiveFeature u) +
          conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse u *
            dslope carryMaterialReducedResponse t u := by
  have hphi : AnalyticAt ℂ positiveFeature 0 :=
    sourceAxis_analyticAt_zero.div analyticAt_const
      (by exact_mod_cast (Real.sqrt_pos.mpr sourceScale_pos).ne')
  have hreg := (real_regular_germ material_source_response_eventually_eq sourceResponse_analyticAt_zero).and
    ((real_regular_germ material_reduced_eventually_eq reducedResponse_analyticAt_zero).and
      (real_regular_germ material_feature_eventually_eq hphi))
  rcases material_real_kernel_split_offdiag with ⟨V, hV, hV0, hsplit⟩
  rcases mem_nhds_iff.mp hreg with ⟨W, hW, hWo, hW0⟩
  let U := V ∩ W
  have hUo : IsOpen U := hV.inter hWo
  refine ⟨U, hUo, ⟨hV0,hW0⟩, ?_⟩
  intro t ht u hu
  by_cases hne : u ≠ t
  · exact hsplit t ht.1 u hu.1 hne
  · have he : u = t := not_ne_iff.mp hne
    subst u
    have hl : ContinuousAt (dslope carryMaterialNormalizedResponse t) t :=
      continuousAt_dslope_same.mpr (hW ht.2).1.differentiableAt
    have hb : ContinuousAt (dslope carryMaterialReducedResponse t) t :=
      continuousAt_dslope_same.mpr (hW ht.2).2.1.differentiableAt
    have hp := (hW ht.2).2.2.continuousAt
    have hr : ContinuousAt (fun u =>
        inner ℂ (carryMaterialPositiveFeature t) (carryMaterialPositiveFeature u) +
          conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse u *
            dslope carryMaterialReducedResponse t u) t := by
      apply ContinuousAt.add
      · have hc := hp.mul (show ContinuousAt (fun _ : ℝ => conj (carryMaterialPositiveFeature t)) t from continuousAt_const)
        change ContinuousAt (fun u : ℝ => carryMaterialPositiveFeature u * conj (carryMaterialPositiveFeature t)) t at hc
        simpa only [RCLike.inner_apply] using hc
      · exact (continuousAt_const.mul (hW ht.2).1.continuousAt).mul hb
    have heq : (dslope carryMaterialNormalizedResponse t) =ᶠ[nhdsWithin t {t}ᶜ]
        (fun u => inner ℂ (carryMaterialPositiveFeature t) (carryMaterialPositiveFeature u) +
          conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse u *
            dslope carryMaterialReducedResponse t u) := by
      have hmem : ∀ᶠ u : ℝ in nhds t, u ∈ U := hUo.mem_nhds ht
      filter_upwards [self_mem_nhdsWithin, hmem.filter_mono nhdsWithin_le_nhds]
        with u hne hu
      exact hsplit t ht.1 u hu.1 (by simpa using hne)
    exact tendsto_nhds_unique
      ((hl.tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
      (hr.tendsto.mono_left nhdsWithin_le_nhds)

/-- A finite real source family includes every diagonal and every ordered
crossing, in one neighborhood independent of the family size. -/
theorem material_real_finite_energy_split :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ (N : ℕ) (c : Fin N → ℂ) (t : Fin N → ℝ), (∀ i, t i ∈ U) →
        ∑ i, ∑ j, conj (c i)*c j*dslope carryMaterialNormalizedResponse (t i) (t j) =
          (‖∑ i, c i*carryMaterialPositiveFeature (t i)‖^2 : ℂ) +
          ∑ i, ∑ j, conj (c i*carryMaterialNormalizedResponse (t i))*
            (c j*carryMaterialNormalizedResponse (t j))*dslope carryMaterialReducedResponse (t i) (t j) := by
  rcases material_real_kernel_split with ⟨U, ho, hz, hU⟩
  refine ⟨U, ho, hz, ?_⟩
  intro N c t ht
  have hGram : (‖∑ i, c i*carryMaterialPositiveFeature (t i)‖^2 : ℂ) =
      ∑ i, ∑ j, conj (c i)*c j*inner ℂ (carryMaterialPositiveFeature (t i))
        (carryMaterialPositiveFeature (t j)) := by
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.inner_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hGram, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hU (t i) (ht i) (t j) (ht j), map_mul]
  ring

private theorem deriv_real_germ {f : ℝ → ℂ} {g : ℂ → ℂ}
    (he : f =ᶠ[nhds 0] fun t : ℝ => g (t : ℂ)) (hg : AnalyticAt ℂ g 0) :
    deriv f =ᶠ[nhds 0] fun t : ℝ => deriv g (t : ℂ) := by
  filter_upwards [real_regular_germ he hg] with t ht
  exact ht.deriv

theorem material_reduced_deriv_continuous : ContinuousAt (deriv carryMaterialReducedResponse) 0 := by
  have he := deriv_real_germ material_reduced_eventually_eq reducedResponse_analyticAt_zero
  have hco : ContinuousAt (fun t : ℝ => (t : ℂ)) 0 := Complex.continuous_ofReal.continuousAt
  have hcd : ContinuousAt (deriv reducedResponse) ((0 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_zero] using reducedResponse_analyticAt_zero.deriv.continuousAt
  have hc : ContinuousAt (fun t : ℝ => deriv reducedResponse (t : ℂ)) 0 := hcd.comp' hco
  exact hc.congr he.symm

/-- The weighted residual vanishes on the central row but is strictly
positive on every sufficiently small NONZERO real diagonal. This is a
pointwise sign theorem, not positive semidefiniteness of all finite Grams. -/
theorem material_weighted_residual_diagonal_pos :
    ∀ᶠ t : ℝ in nhds 0, t ≠ 0 →
      0 < (conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse t *
        dslope carryMaterialReducedResponse t t).re := by
  have hc : ContinuousAt carryMaterialResponseAxis 0 :=
    (sourceAxis_analyticAt_zero.differentiableAt.hasDerivAt.comp_ofReal.congr_of_eventuallyEq
      material_axis_eventually_eq).continuousAt
  have hne : carryMaterialResponseAxis 0 ≠ 0 := by
    rw [material_axis_zero]
    exact Complex.ofReal_ne_zero.mpr canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
  have hcont : ContinuousAt (fun t : ℝ => (deriv carryMaterialReducedResponse t).re) 0 :=
    Complex.continuous_re.continuousAt.comp' material_reduced_deriv_continuous
  have hp : ∀ᶠ t : ℝ in nhds 0, 0 < (deriv carryMaterialReducedResponse t).re :=
    (tendsto_order.1 hcont).1 0 material_reduced_deriv_real_pos
  filter_upwards [hc.eventually_ne hne, hp] with t ha hb ht
  have he : carryMaterialNormalizedResponse t = (t : ℂ)*carryMaterialResponseAxis t := by
    have h := sub_smul_dslope carryMaterialNormalizedResponse 0 t
    simpa only [sub_zero, material_normalized_response_zero, carryMaterialResponseAxis,
      Complex.real_smul] using h.symm
  have hq : carryMaterialNormalizedResponse t ≠ 0 := by
    rw [he]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) ha
  simpa only [dslope_same, ← Complex.normSq_eq_conj_mul_self, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_pos (Complex.normSq_pos.mpr hq) hb

/-- A calibrated central row cannot justify deleting this residual in any
real neighborhood of the actual source. -/
theorem material_weighted_residual_not_zero_germ :
    ¬ (fun t : ℝ => conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse t *
      dslope carryMaterialReducedResponse t t) =ᶠ[nhds 0] fun _ => (0 : ℂ) := by
  intro hz
  have hp := material_weighted_residual_diagonal_pos
  have hf : ∀ᶠ t : ℝ in nhdsWithin 0 {0}ᶜ, False := by
    filter_upwards [hp.filter_mono nhdsWithin_le_nhds, hz.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht he hne
    have h := ht (by simpa using hne)
    rw [he] at h
    norm_num at h
  rcases hf.exists with ⟨_, h⟩
  exact h

/-- The first jet of the second EXISTING positive channel is transported
from the same material response. Its energy is exactly the genuine h1. -/
theorem material_second_channel_hasDerivAt_zero :
    HasDerivAt (fun t : ℝ => carryMaterialNormalizedResponse t * secondPositiveFeature (t : ℂ))
      ((sourceScale : ℂ)*(Real.sqrt reducedSourceScale : ℂ)) 0 := by
  have he : (fun t : ℝ => carryMaterialNormalizedResponse t * secondPositiveFeature (t : ℂ)) =ᶠ[nhds 0]
      (fun t : ℝ => (sourceResponse * secondPositiveFeature) (t : ℂ)) := by
    filter_upwards [material_source_response_eventually_eq] with t ht
    simp only [Pi.mul_apply, ht]
  exact secondChannel_hasDerivAt_zero.comp_ofReal.congr_of_eventuallyEq he

theorem material_second_channel_firstJet_energy :
    ‖deriv (fun t : ℝ => carryMaterialNormalizedResponse t * secondPositiveFeature (t : ℂ)) 0‖^2 =
      canonicalCompletedNativeLogDerivativeMoment 1 := by
  rw [material_second_channel_hasDerivAt_zero.deriv]
  simpa only [secondChannel_hasDerivAt_zero.deriv] using secondChannel_firstJet_energy

/-- These two residuals cannot be identified literally: the Schur weight
vanishes centrally, while the actual omitted C2-coordinate source does not. -/
theorem material_weighted_residual_not_physical_edge_energy :
    (conj (carryMaterialNormalizedResponse 0)*carryMaterialNormalizedResponse 0 *
      dslope carryMaterialReducedResponse 0 0).re ≠
        ‖baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 0)‖^2 := by
  rw [material_weighted_residual_center]
  have h := carryMaterial_physical_residual_origin_norm_pos
  simp only [Complex.zero_re]
  nlinarith

/-- When a finite family cancels the extracted channel, its complete energy
is exactly the retained residual, with no assumption about its sign. -/
theorem material_real_energy_on_positive_nullspace :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ (N : ℕ) (c : Fin N → ℂ) (t : Fin N → ℝ), (∀ i, t i ∈ U) →
        (∑ i, c i*carryMaterialPositiveFeature (t i)) = 0 →
        ∑ i, ∑ j, conj (c i)*c j*dslope carryMaterialNormalizedResponse (t i) (t j) =
          ∑ i, ∑ j, conj (c i*carryMaterialNormalizedResponse (t i))*
            (c j*carryMaterialNormalizedResponse (t j))*dslope carryMaterialReducedResponse (t i) (t j) := by
  rcases material_real_finite_energy_split with ⟨U, ho, hz, hU⟩
  refine ⟨U, ho, hz, ?_⟩
  intro N c t ht hcancel
  simpa only [hcancel, norm_zero, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero, zero_add] using
    hU N c t ht

end
end CarryMaterialResidualComparison

namespace CarryMaterialResidualComparison
#assert_central_comparison_axioms material_reduced_eventually_eq
#print axioms material_reduced_eventually_eq
#assert_central_comparison_axioms material_reduced_zero
#print axioms material_reduced_zero
#assert_central_comparison_axioms material_reduced_hasDerivAt_zero
#print axioms material_reduced_hasDerivAt_zero
#assert_central_comparison_axioms material_reduced_deriv_real_pos
#print axioms material_reduced_deriv_real_pos
#assert_central_comparison_axioms material_reduced_not_zero_germ
#print axioms material_reduced_not_zero_germ
#assert_central_comparison_axioms material_response_conj
#print axioms material_response_conj
#assert_central_comparison_axioms material_axis_conj
#print axioms material_axis_conj
#assert_central_comparison_axioms material_reduced_conj
#print axioms material_reduced_conj
#assert_central_comparison_axioms material_weighted_residual_center
#print axioms material_weighted_residual_center
#assert_central_comparison_axioms material_real_kernel_split_offdiag
#print axioms material_real_kernel_split_offdiag
#assert_central_comparison_axioms material_real_kernel_split
#print axioms material_real_kernel_split
#assert_central_comparison_axioms material_real_finite_energy_split
#print axioms material_real_finite_energy_split
#assert_central_comparison_axioms material_reduced_deriv_continuous
#print axioms material_reduced_deriv_continuous
#assert_central_comparison_axioms material_weighted_residual_diagonal_pos
#print axioms material_weighted_residual_diagonal_pos
#assert_central_comparison_axioms material_weighted_residual_not_zero_germ
#print axioms material_weighted_residual_not_zero_germ
#assert_central_comparison_axioms material_second_channel_hasDerivAt_zero
#print axioms material_second_channel_hasDerivAt_zero
#assert_central_comparison_axioms material_second_channel_firstJet_energy
#print axioms material_second_channel_firstJet_energy
#assert_central_comparison_axioms material_weighted_residual_not_physical_edge_energy
#print axioms material_weighted_residual_not_physical_edge_energy
#assert_central_comparison_axioms material_real_energy_on_positive_nullspace
#print axioms material_real_energy_on_positive_nullspace
end CarryMaterialResidualComparison

namespace CarryMaterialCentralProjectionComparison
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Coarse bound from existing raw theta integral certificates, not numerical
fitting or a new moment source. -/
theorem canonical_first_shifted_moment_lt :
    canonicalCompletedNativeLogDerivativeMoment 1 < (1/1024 : ℝ) := by
  have he := nativeSourceOddBoundaryCoefficient_integral_formulas.2.1
  rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical] at he
  rcases nativeSourceCosineIntegral_refined_box with ⟨ha, _, hb, hbu, hc, _⟩
  have hap : 0 < completedNativeXiCosineMoment 0 := by linarith
  have hbp : 0 < completedNativeXiCosineMoment 1 := by linarith
  have hcp : 0 < completedNativeXiCosineMoment 2 := by linarith
  have hbs : completedNativeXiCosineMoment 1 ^ 2 < (23/1000 : ℝ)^2 := by nlinarith
  have has : (49/100 : ℝ)^2 < completedNativeXiCosineMoment 0 ^ 2 := by nlinarith
  have hac := mul_pos hap hcp
  have ht : (3 * completedNativeXiCosineMoment 1^2 -
      completedNativeXiCosineMoment 0 * completedNativeXiCosineMoment 2) /
      (6*completedNativeXiCosineMoment 0^2) < (1/512 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  linarith

/-- The proposed central-plane deflation fails the genuine first-jet test.
This rejects this candidate only, without changing its metric or scale. -/
theorem material_centered_firstJet_gap :
    (1/1024 : ℝ) < ‖deriv carryMaterialCenteredState 0‖^2 -
      canonicalCompletedNativeLogDerivativeMoment 1 := by
  linarith [carryMaterialCenteredState_firstJet_energy_gt, canonical_first_shifted_moment_lt]

theorem material_centered_firstJet_ne_canonical :
    ‖deriv carryMaterialCenteredState 0‖^2 ≠ canonicalCompletedNativeLogDerivativeMoment 1 := by
  linarith [material_centered_firstJet_gap]

open CarryMaterialResidualComparison CarryMaterialResponseComparison Filter
open scoped Topology ComplexConjugate

/-- Equality of the actual residual diagonals forces the first mixed jet.
No identification of vertical coordinates with jets is used. -/
theorem material_centered_residual_firstJet_necessary
    (h : (fun t : ℝ => (‖carryMaterialCenteredState t‖^2 : ℂ)) =ᶠ[nhds 0]
      (fun t => conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse t *
        dslope carryMaterialReducedResponse t t)) :
    ‖deriv carryMaterialCenteredState 0‖^2 = canonicalCompletedNativeLogDerivativeMoment 1 := by
  have hG : ContinuousAt (fun t : ℝ => ‖dslope carryMaterialCenteredState 0 t‖^2) 0 :=
    (continuousAt_dslope_same.mpr carryMaterialCenteredState_hasDerivAt_zero.differentiableAt).norm.pow 2
  have ha : ContinuousAt carryMaterialResponseAxis 0 :=
    (SourcePositiveReduction.sourceAxis_analyticAt_zero.differentiableAt.hasDerivAt.comp_ofReal.congr_of_eventuallyEq
      material_axis_eventually_eq).continuousAt
  have hF : ContinuousAt (fun t : ℝ => ‖carryMaterialResponseAxis t‖^2 *
      (deriv carryMaterialReducedResponse t).re) 0 :=
    (ha.norm.pow 2).mul (Complex.continuous_re.continuousAt.comp' material_reduced_deriv_continuous)
  have heq : (fun t : ℝ => ‖dslope carryMaterialCenteredState 0 t‖^2) =ᶠ[nhdsWithin 0 {0}ᶜ]
      (fun t : ℝ => ‖carryMaterialResponseAxis t‖^2 * (deriv carryMaterialReducedResponse t).re) := by
    filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hne
    have hn : t ≠ 0 := by simpa using hne
    have hZ : ‖carryMaterialCenteredState t‖^2 = t^2*‖dslope carryMaterialCenteredState 0 t‖^2 := by
      have hr : carryMaterialCenteredState t = t • dslope carryMaterialCenteredState 0 t := by
        simpa only [sub_zero, carryMaterialCenteredState_zero] using
          (sub_smul_dslope carryMaterialCenteredState 0 t).symm
      rw [hr, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hq : ‖carryMaterialNormalizedResponse t‖^2 = t^2*‖carryMaterialResponseAxis t‖^2 := by
      have hr : carryMaterialNormalizedResponse t = t • carryMaterialResponseAxis t := by
        simpa only [sub_zero, material_normalized_response_zero, carryMaterialResponseAxis] using
          (sub_smul_dslope carryMaterialNormalizedResponse 0 t).symm
      rw [hr, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hh : ‖carryMaterialCenteredState t‖^2 =
        ‖carryMaterialNormalizedResponse t‖^2*(deriv carryMaterialReducedResponse t).re := by
      have hr := congrArg Complex.re ht
      simp only [← Complex.ofReal_pow, Complex.ofReal_re, dslope_same, ← Complex.normSq_eq_conj_mul_self,
        Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, ← Complex.sq_norm] at hr
      change ‖carryMaterialCenteredState t‖^2 =
        ‖carryMaterialNormalizedResponse t‖^2*(deriv carryMaterialReducedResponse t).re at hr
      exact hr
    rw [hZ, hq, mul_assoc] at hh
    exact mul_left_cancel₀ (pow_ne_zero 2 hn) hh
  have hv := tendsto_nhds_unique
    ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
    (hF.tendsto.mono_left nhdsWithin_le_nhds)
  have hFzero : ‖carryMaterialResponseAxis 0‖^2*(deriv carryMaterialReducedResponse 0).re =
      canonicalCompletedNativeLogDerivativeMoment 1 := by
    rw [material_axis_zero, material_reduced_hasDerivAt_zero.deriv]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Complex.ofReal_pow,
      ← Complex.ofReal_div, Complex.ofReal_re]
    field_simp [canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne']
  simpa only [dslope_same, hFzero] using hv

/-- Narrow no-go: this actual projected source cannot equal the weighted
canonical residual even just on a real diagonal germ. -/
theorem material_centered_not_residual_diagonal_germ :
    ¬ (fun t : ℝ => (‖carryMaterialCenteredState t‖^2 : ℂ)) =ᶠ[nhds 0]
      (fun t => conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse t *
        dslope carryMaterialReducedResponse t t) := by
  intro h
  exact material_centered_firstJet_ne_canonical (material_centered_residual_firstJet_necessary h)

end
end CarryMaterialCentralProjectionComparison

namespace CarryMaterialCentralProjectionComparison
#assert_central_comparison_axioms canonical_first_shifted_moment_lt
#print axioms canonical_first_shifted_moment_lt
#assert_central_comparison_axioms material_centered_firstJet_gap
#print axioms material_centered_firstJet_gap
#assert_central_comparison_axioms material_centered_firstJet_ne_canonical
#print axioms material_centered_firstJet_ne_canonical
#assert_central_comparison_axioms material_centered_residual_firstJet_necessary
#print axioms material_centered_residual_firstJet_necessary
#assert_central_comparison_axioms material_centered_not_residual_diagonal_germ
#print axioms material_centered_not_residual_diagonal_germ
end CarryMaterialCentralProjectionComparison
