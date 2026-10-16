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
