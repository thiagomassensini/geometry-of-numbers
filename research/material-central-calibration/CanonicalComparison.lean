import GeometryOfNumbers.Analysis.CarryMaterialFourthPivot
import GeometryOfNumbers.Analysis.CarryMaterialSourceFactor
import GeometryOfNumbers.Analysis.CarryMaterialMixedSchur
import CarrySelfAdjointOperator.NativeSourceSchurThetaIntegral
import GeometryOfNumbers.Analysis.CarryMaterialProjectiveReturnGreen
import GeometryOfNumbers.Analysis.CarryMaterialClockCentralCoupling
import CarrySelfAdjointOperator.NativeThetaAdaptiveBudget
import CarrySelfAdjointOperator.AllOrderLogJetLedger
import CarrySelfAdjointOperator.CompletedNativeSixthOrderThetaPositivity
import CarrySelfAdjointOperator.CompletedNativeChiralReturnFourteenthSourceIntegral
import CarrySelfAdjointOperator.NativeSourceThetaGreenTransport
import GeometryOfNumbers.Analysis.CarryMaterialNullHierarchy
import CarrySelfAdjointOperator.CompletedNativeChiralReturnTenthSourceIntegral
import GeometryOfNumbers.Analysis.CarryMaterialThirdNullSector
import CarrySelfAdjointOperator.NativeCompletedSourceFourthPositiveChannel
import GeometryOfNumbers.Analysis.CarryMaterialSecondNullSector
import CarrySelfAdjointOperator.NativeCompletedSourceThirdPositiveChannel
import GeometryOfNumbers.Analysis.CarryMaterialResidualPositiveTransport
import GeometryOfNumbers.Analysis.CarryMaterialCompanionGreenTransport
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

namespace CarryMaterialGreenPairComparison
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator CarryMaterialResponseComparison CarryMaterialResidualComparison
open Filter
open scoped InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Literal sign/order calibration against the existing boundary API. -/
theorem material_pair_green_eq_existing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E × E) : carryMaterialPairGreen x y =
      NativeCarrySpectralWeyl.Boundary.greenForm (𝕜 := ℂ) x y := rfl

theorem material_pair_readout_native (t : ℝ) :
    carryMaterialPairReadout (carryMaterialCompanionValuePair t) =
      ((canonicalCompletedC3ScalarBoundaryPair (t : ℂ)).1,
        2*(canonicalCompletedC3ScalarBoundaryPair (t : ℂ)).2) := by
  apply Prod.ext
  · exact material_companion t
  · simp only [carryMaterialPairReadout, carryMaterialCompanionValuePair, map_smul,
      carryMaterial_dressed_completed_readout, smul_eq_mul,
      CarryMaterialCanonicalComparison.material_response]
    rfl

/-- Signed physical Green balance equals the existing completed Wronskian.
This is not an equality of positive Hilbert Gram kernels. -/
theorem material_pair_corrected_green (t u : ℝ) :
    carryMaterialPairGreen (carryMaterialCompanionValuePair t) (carryMaterialCompanionValuePair u) -
      carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialCompanionValuePair t))
        (carryMaterialPairComplement (carryMaterialCompanionValuePair u)) =
      completedGreenWronskian completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion
        (u : ℂ) (t : ℂ) := by
  have h := carryMaterialPairGreen_readout_ledger
    (carryMaterialCompanionValuePair t) (carryMaterialCompanionValuePair u)
  rw [material_pair_readout_native t, material_pair_readout_native u] at h
  rw [completedGreenWronskian_eq_scalarGreenForm]
  simp only [carryMaterialPairGreen, canonicalCompletedC3ScalarBoundaryPair,
    NativeCarrySpectralWeyl.Boundary.greenForm, RCLike.inner_apply, map_mul, map_ofNat] at h ⊢
  linear_combination h

theorem material_companion_center_readout_zero :
    baseTwoCompletedBoundaryHilbertReadout (carryMaterialCompanionValuePair 0).1 = 0 := by
  have h := material_normalized_response_zero
  rw [carryMaterialNormalizedResponse_eq] at h
  have hf : baseTwoCanonicalResponse 0 ≠ 0 := by
    rw [baseTwoCanonicalResponse_eq_dressing_mul_signal]
    exact mul_ne_zero (baseTwoCanonicalDressingScalar_ne_zero 0) carryMaterial_origin_signal_ne_zero
  have hd := (div_eq_zero_iff.mp h).resolve_right (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hf)
  change baseTwoCompletedBoundaryHilbertReadout (carryMaterialDressedCompanion 0
    ⟨baseTwoCompletedBoundaryHilbertState 0, baseTwoCompletedBoundaryHilbertState_mem_clockDomain 0⟩) = 0
  rw [carryMaterialDressedCompanion_source_readout]
  exact hd

theorem material_companion_hidden_center :
    carryMaterialReadoutComplement (carryMaterialCompanionValuePair 0).1 =
      (carryMaterialCompanionValuePair 0).1 ∧
    0 < ‖carryMaterialReadoutComplement (carryMaterialCompanionValuePair 0).1‖ := by
  have he := carryMaterialReadoutComplement_of_readout_zero _ material_companion_center_readout_zero
  exact ⟨he, by rw [he]; exact norm_pos_iff.mpr carryMaterialCompanion_center_ne_zero⟩

theorem material_reduced_pair_center_invisible_nonzero :
    carryMaterialPairReadout (carryMaterialReducedCompanionPair 0) = 0 ∧
      carryMaterialReducedCompanionPair 0 ≠ 0 := by
  constructor
  · simp only [carryMaterialReducedCompanionPair_zero, carryMaterialPairReadout,
      material_companion_center_readout_zero, map_zero, Prod.zero_eq_mk]
  · intro h
    have he := congrArg Prod.fst h
    rw [carryMaterialReducedCompanionPair_zero] at he
    exact carryMaterialCompanion_center_ne_zero he

theorem material_reduced_centering_readout (t : ℝ) :
    carryMaterialPairReadout (carryMaterialReducedCenteredPair t) =
      carryMaterialPairReadout (carryMaterialReducedCompanionPair t) := by
  simp only [carryMaterialPairReadout, carryMaterialReducedCenteredPair, map_sub,
    material_companion_center_readout_zero, sub_zero]

/-- Source reduction, before division and including the removable center. -/
theorem material_reduced_pair_homogeneous :
    ∀ᶠ t : ℝ in nhds 0,
      baseTwoCompletedBoundaryHilbertReadout (carryMaterialReducedCompanionPair t).1 =
        baseTwoCompletedBoundaryHilbertReadout (carryMaterialReducedCompanionPair t).2 *
          carryMaterialReducedResponse t := by
  have hc : Tendsto (fun t : ℝ => (t : ℂ)) (nhds 0) (nhds 0) := by
    simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.tendsto 0
  have hf0 : baseTwoCanonicalResponse 0 ≠ 0 := by
    rw [baseTwoCanonicalResponse_eq_dressing_mul_signal]
    exact mul_ne_zero (baseTwoCanonicalDressingScalar_ne_zero 0) carryMaterial_origin_signal_ne_zero
  have hfn := (baseTwoCanonicalResponse_analyticAt 0).continuousAt.eventually_ne hf0
  filter_upwards [material_source_response_eventually_eq, material_reduced_eventually_eq,
    hc.eventually SourcePositiveReduction.sourceAxis_eventually_ne_zero, hfn] with t hr hb ha hf
  have hs : carryMaterialResponseScale = SourcePositiveReduction.sourceScale := by
    rw [material_scale_eq, SourcePositiveReduction.sourceScale_eq]
  have he := SourcePositiveReduction.sourceResponse_reconstruction (t : ℂ) ha
  have hre : carryMaterialNormalizedResponse t *
      (1-(carryMaterialResponseScale : ℂ)*(t : ℂ)*carryMaterialReducedResponse t) =
        (carryMaterialResponseScale : ℂ)*(t : ℂ) := by
    simpa only [hr, hb, hs] using he
  have hp := congrArg Prod.fst (carryMaterialCompanionValuePair_readout t)
  have hq := congrArg Prod.snd (carryMaterialCompanionValuePair_readout t)
  change baseTwoCompletedBoundaryHilbertReadout (carryMaterialCompanionValuePair t).1 =
    -deriv baseTwoCanonicalResponse t at hp
  change baseTwoCompletedBoundaryHilbertReadout (carryMaterialCompanionValuePair t).2 =
    2*baseTwoCanonicalResponse t at hq
  have hpq : baseTwoCompletedBoundaryHilbertReadout (carryMaterialCompanionValuePair t).1 =
      (2*baseTwoCanonicalResponse t)*carryMaterialNormalizedResponse t := by
    rw [hp, carryMaterialNormalizedResponse_eq]
    field_simp
  change baseTwoCompletedBoundaryHilbertReadout ((carryMaterialCompanionValuePair t).1-
      ((carryMaterialResponseScale*t : ℝ) : ℂ) • (carryMaterialCompanionValuePair t).2) =
    baseTwoCompletedBoundaryHilbertReadout (((carryMaterialResponseScale*t : ℝ) : ℂ) •
      (carryMaterialCompanionValuePair t).1) * carryMaterialReducedResponse t
  rw [map_sub, map_smul, map_smul, hpq, hq]
  simp only [smul_eq_mul, Complex.ofReal_mul]
  linear_combination (2*baseTwoCanonicalResponse t)*hre

/-- The new denominator is an actual companion readout, with its clock and
completion derivative; its factorization is local where F is nonzero. -/
theorem material_reduced_pair_denominator :
    ∀ᶠ t : ℝ in nhds 0,
      baseTwoCompletedBoundaryHilbertReadout (carryMaterialReducedCompanionPair t).2 =
        (2 : ℂ)*((carryMaterialResponseScale*t : ℝ) : ℂ)*
          baseTwoCanonicalResponse t*carryMaterialNormalizedResponse t := by
  have hf0 : baseTwoCanonicalResponse 0 ≠ 0 := by
    rw [baseTwoCanonicalResponse_eq_dressing_mul_signal]
    exact mul_ne_zero (baseTwoCanonicalDressingScalar_ne_zero 0) carryMaterial_origin_signal_ne_zero
  filter_upwards [(baseTwoCanonicalResponse_analyticAt 0).continuousAt.eventually_ne hf0] with t hf
  change baseTwoCompletedBoundaryHilbertReadout (((carryMaterialResponseScale*t : ℝ) : ℂ) •
    (carryMaterialCompanionValuePair t).1) = _
  rw [map_smul]
  change ((carryMaterialResponseScale*t : ℝ) : ℂ)*
    baseTwoCompletedBoundaryHilbertReadout (carryMaterialDressedCompanion t
      ⟨baseTwoCompletedBoundaryHilbertState t, baseTwoCompletedBoundaryHilbertState_mem_clockDomain t⟩) = _
  rw [carryMaterialDressedCompanion_source_readout, carryMaterialNormalizedResponse_eq]
  field_simp

/-- Exact signed Green realization of the reduced dslope numerator.
Every local diagonal is included; division at collisions is not asserted. -/
theorem material_reduced_pair_green_dslope :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U,
        carryMaterialPairGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u) -
          carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
            (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) =
        (1/2 : ℂ)*conj (baseTwoCompletedBoundaryHilbertReadout (carryMaterialReducedCompanionPair t).2)*
          baseTwoCompletedBoundaryHilbertReadout (carryMaterialReducedCompanionPair u).2 *
            ((u-t : ℝ) : ℂ)*dslope carryMaterialReducedResponse t u := by
  rcases mem_nhds_iff.mp material_reduced_pair_homogeneous with ⟨U, hU, ho, hz⟩
  refine ⟨U, ho, hz, ?_⟩
  intro t ht u hu
  have hpt := hU ht
  have hpu := hU hu
  have h := carryMaterialPairGreen_readout_ledger
    (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u)
  have hg : carryMaterialPairGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u) -
      carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
        (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) =
      (1/2 : ℂ)*carryMaterialPairGreen
        (carryMaterialPairReadout (carryMaterialReducedCompanionPair t))
        (carryMaterialPairReadout (carryMaterialReducedCompanionPair u)) := by
    linear_combination h
  rw [hg]
  simp only [carryMaterialPairGreen, carryMaterialPairReadout, RCLike.inner_apply]
  rw [hpt, hpu]
  simp only [map_mul, material_reduced_conj]
  have hs : ((u-t : ℝ) : ℂ)*dslope carryMaterialReducedResponse t u =
      carryMaterialReducedResponse u-carryMaterialReducedResponse t := by
    simpa only [Complex.real_smul] using sub_smul_dslope carryMaterialReducedResponse t u
  linear_combination
    -((1/2 : ℂ)*conj (baseTwoCompletedBoundaryHilbertReadout (carryMaterialReducedCompanionPair t).2)*
      baseTwoCompletedBoundaryHilbertReadout (carryMaterialReducedCompanionPair u).2)*hs

/-- The same canonical weighted residual as PR #6, derived from the full
physical companion/value pair with its explicit null-readout Green balance. -/
theorem material_reduced_pair_canonical_residual_numerator :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U,
        carryMaterialPairGreen (carryMaterialReducedCompanionPair t) (carryMaterialReducedCompanionPair u) -
          carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
            (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) =
        (2 : ℂ)*((carryMaterialResponseScale^2*t*u : ℝ) : ℂ)*
          conj (baseTwoCanonicalResponse t)*baseTwoCanonicalResponse u*((u-t : ℝ) : ℂ)*
            (conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse u *
              dslope carryMaterialReducedResponse t u) := by
  rcases material_reduced_pair_green_dslope with ⟨V, hVo, hVz, hV⟩
  rcases mem_nhds_iff.mp material_reduced_pair_denominator with ⟨W, hW, hWo, hWz⟩
  refine ⟨V ∩ W, hVo.inter hWo, ⟨hVz,hWz⟩, ?_⟩
  intro t ht u hu
  rw [hV t ht.1 u hu.1, hW ht.2, hW hu.2]
  simp only [map_mul, map_ofNat, Complex.conj_ofReal]
  push_cast
  ring

end
end CarryMaterialGreenPairComparison

namespace CarryMaterialGreenPairComparison
#assert_central_comparison_axioms material_pair_green_eq_existing
#print axioms material_pair_green_eq_existing
#assert_central_comparison_axioms material_pair_readout_native
#print axioms material_pair_readout_native
#assert_central_comparison_axioms material_pair_corrected_green
#print axioms material_pair_corrected_green
#assert_central_comparison_axioms material_companion_center_readout_zero
#print axioms material_companion_center_readout_zero
#assert_central_comparison_axioms material_companion_hidden_center
#print axioms material_companion_hidden_center
#assert_central_comparison_axioms material_reduced_pair_center_invisible_nonzero
#print axioms material_reduced_pair_center_invisible_nonzero
#assert_central_comparison_axioms material_reduced_centering_readout
#print axioms material_reduced_centering_readout
#assert_central_comparison_axioms material_reduced_pair_homogeneous
#print axioms material_reduced_pair_homogeneous
#assert_central_comparison_axioms material_reduced_pair_denominator
#print axioms material_reduced_pair_denominator
#assert_central_comparison_axioms material_reduced_pair_green_dslope
#print axioms material_reduced_pair_green_dslope
#assert_central_comparison_axioms material_reduced_pair_canonical_residual_numerator
#print axioms material_reduced_pair_canonical_residual_numerator
end CarryMaterialGreenPairComparison

namespace CarryMaterialPositiveResidualComparison
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator CarrySelfAdjointOperator.SourcePositiveReduction
open CarryMaterialResponseComparison CarryMaterialResidualComparison
open Filter
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem real_dslope_conj (f : ℝ → ℂ) (h : ∀ t, conj (f t) = f t) (t u : ℝ) :
    conj (dslope f t u) = dslope f t u := by
  have he : Complex.conjCLE.toContinuousLinearMap ∘ f = f := by
    funext t
    exact h t
  by_cases htu : t = u
  · subst u
    by_cases hd : DifferentiableAt ℝ f t
    · have hh := Complex.conjCLE.toContinuousLinearMap.dslope_comp f t t (fun _ => hd)
      rw [he] at hh
      exact hh.symm
    · simp only [dslope_same, deriv_zero_of_not_differentiableAt hd, map_zero]
  · have hh := Complex.conjCLE.toContinuousLinearMap.dslope_comp f t u
      (fun heq => False.elim (htu heq))
    rw [he] at hh
    exact hh.symm

theorem material_real_kernel_coe (t u : ℝ) :
    (carryMaterialRealKernel t u : ℂ) = dslope carryMaterialNormalizedResponse t u := by
  exact Complex.conj_eq_iff_re.mp (real_dslope_conj _ material_response_conj t u)

theorem material_real_residual_coe (t u : ℝ) :
    (carryMaterialRealResidual t u : ℂ) =
      conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse u*
        dslope carryMaterialReducedResponse t u := by
  apply Complex.conj_eq_iff_re.mp
  simp only [Complex.star_def, map_mul, material_response_conj,
    real_dslope_conj _ material_reduced_conj]

theorem material_real_feature_coe (t : ℝ) :
    (carryMaterialRealFeature t : ℂ) = carryMaterialPositiveFeature t := by
  apply Complex.conj_eq_iff_re.mp
  simp only [carryMaterialPositiveFeature, map_div₀, Complex.conj_ofReal, material_axis_conj]

theorem material_real_feature_zero :
    carryMaterialRealFeature 0 = Real.sqrt carryMaterialResponseScale := by
  unfold carryMaterialRealFeature carryMaterialPositiveFeature
  rw [material_axis_zero, ← material_scale_eq]
  have hp := material_scale_pos
  have hs := Real.sq_sqrt hp.le
  have hn := (Real.sqrt_pos.mpr hp).ne'
  simp only [Complex.div_ofReal_re, Complex.ofReal_re]
  apply (div_eq_iff hn).mpr
  nlinarith

theorem material_real_feature_zero_pos : 0 < carryMaterialRealFeature 0 := by
  rw [material_real_feature_zero]
  exact Real.sqrt_pos.mpr material_scale_pos

theorem material_real_residual_zero_left (t : ℝ) : carryMaterialRealResidual 0 t = 0 := by
  simp [carryMaterialRealResidual, material_normalized_response_zero]

theorem material_real_residual_zero_right (t : ℝ) : carryMaterialRealResidual t 0 = 0 := by
  simp [carryMaterialRealResidual, material_normalized_response_zero]

theorem material_real_kernel_split :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U, carryMaterialRealKernel t u =
        carryMaterialRealFeature t*carryMaterialRealFeature u + carryMaterialRealResidual t u := by
  rcases CarryMaterialResidualComparison.material_real_kernel_split with ⟨U, ho, hz, h⟩
  refine ⟨U, ho, hz, ?_⟩
  intro t ht u hu
  have he := congrArg Complex.re (h t ht u hu)
  rw [← material_real_feature_coe t, ← material_real_feature_coe u] at he
  simpa only [carryMaterialRealKernel, carryMaterialRealResidual, Complex.add_re,
    RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.star_def, mul_comm] using he

/-- Adding the same canonical source at zero is an exact finite reduction,
not a new field, a positive-kernel hypothesis or a dimension cutoff. -/
theorem material_centered_test_energy :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ (n : ℕ) (c t : Fin n → ℝ), (∀ i, t i ∈ U) →
        carryRealKernelEnergy carryMaterialRealKernel (carryMaterialCenteredCoefficients c t)
          (carryMaterialCenteredParameters t) = carryRealKernelEnergy carryMaterialRealResidual c t := by
  rcases material_real_kernel_split with ⟨U, ho, hz, h⟩
  refine ⟨U, ho, hz, ?_⟩
  intro n c t ht
  exact carryMaterialReal_centered_energy hz material_real_feature_zero_pos.ne' h
    material_real_residual_zero_left material_real_residual_zero_right c t ht

/-- A single source neighborhood, and every central subset of it. Both
sign obligations concern ALL finite real families, including every diagonal. -/
theorem material_full_residual_nonnegative_iff :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ V ⊆ U, (0 : ℝ) ∈ V →
        (CarryRealKernelNonnegativeOn carryMaterialRealKernel V ↔
          CarryRealKernelNonnegativeOn carryMaterialRealResidual V) := by
  rcases material_real_kernel_split with ⟨U, ho, hz, h⟩
  refine ⟨U, ho, hz, ?_⟩
  intro V hV hzV
  exact carryMaterialReal_nonnegative_iff hzV material_real_feature_zero_pos.ne'
    (fun t ht u hu => h t (hV ht) u (hV hu))
    material_real_residual_zero_left material_real_residual_zero_right

/-- Conditional extraction from a GIVEN positive realization of the FULL
kernel, using its central direction and the inherited real inner product. -/
theorem material_extract_residual_of_full_realization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ v : ℝ → H, (∀ t ∈ U, ∀ u ∈ U, inner ℝ (v t) (v u) = carryMaterialRealKernel t u) →
        ∀ t ∈ U, ∀ u ∈ U,
          inner ℝ (carryMaterialRealOrthogonalResidual v t) (carryMaterialRealOrthogonalResidual v u) =
            carryMaterialRealResidual t u := by
  rcases material_real_kernel_split with ⟨U, ho, hz, h⟩
  refine ⟨U, ho, hz, ?_⟩
  intro v hv t ht u hu
  have h00 : inner ℝ (v 0) (v 0) = carryMaterialRealFeature 0^2 := by
    rw [hv 0 hz 0 hz, h 0 hz 0 hz, material_real_residual_zero_left, add_zero, pow_two]
  have ht0 : inner ℝ (v t) (v 0) = carryMaterialRealFeature t*carryMaterialRealFeature 0 := by
    rw [hv t ht 0 hz, h t ht 0 hz, material_real_residual_zero_right, add_zero]
  have h0u : inner ℝ (v 0) (v u) = carryMaterialRealFeature 0*carryMaterialRealFeature u := by
    rw [hv 0 hz u hu, h 0 hz u hu, material_real_residual_zero_left, add_zero]
  rw [carryMaterialRealOrthogonalResidual_pairing v t u material_real_feature_zero_pos.ne' h00 ht0 h0u,
    hv t ht u hu, h t ht u hu]
  ring

/-- A residual realization assembles the full kernel in the inherited
real direct sum. This does NOT assert existence of the residual input. -/
theorem material_lift_full_of_residual_realization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ v : ℝ → H, (∀ t ∈ U, ∀ u ∈ U, inner ℝ (v t) (v u) = carryMaterialRealResidual t u) →
        ∀ t ∈ U, ∀ u ∈ U,
          inner ℝ (carryMaterialRealKernelLift v t) (carryMaterialRealKernelLift v u) =
            carryMaterialRealKernel t u := by
  rcases material_real_kernel_split with ⟨U, ho, hz, h⟩
  refine ⟨U, ho, hz, ?_⟩
  intro v hv t ht u hu
  rw [carryMaterialRealKernelLift_pairing, hv t ht u hu, h t ht u hu]

/-- The central zero is compulsory for ANY real residual realization. -/
theorem material_residual_realization_center_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v : ℝ → H)
    (hv : inner ℝ (v 0) (v 0) = carryMaterialRealResidual 0 0) : v 0 = 0 := by
  rw [material_real_residual_zero_left] at hv
  exact inner_self_eq_zero.mp hv

/-- Specific source obstruction: a realization of the normalized residual
cannot also preserve the complete raw reduced-pair energy at the center. -/
theorem material_residual_not_raw_reduced_pair_energy
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v : ℝ → H)
    (hv : inner ℝ (v 0) (v 0) = carryMaterialRealResidual 0 0) :
    ‖v 0‖^2 ≠ ‖(carryMaterialReducedCompanionPair 0).1‖^2 +
      ‖(carryMaterialReducedCompanionPair 0).2‖^2 := by
  rw [material_residual_realization_center_zero v hv, carryMaterialReducedCompanionPair_zero]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  exact (sq_pos_of_pos (norm_pos_iff.mpr carryMaterialCompanion_center_ne_zero)).ne

theorem material_axis_continuous : ContinuousAt carryMaterialResponseAxis 0 := by
  exact (sourceAxis_analyticAt_zero.differentiableAt.hasDerivAt.comp_ofReal.congr_of_eventuallyEq
    material_axis_eventually_eq).continuousAt

/-- The tangent coefficient is precisely the existing canonical h1. -/
theorem material_residual_core_center :
    carryMaterialResidualCore 0 0 = canonicalCompletedNativeLogDerivativeMoment 1 := by
  unfold carryMaterialResidualCore
  rw [material_axis_zero, dslope_same, material_reduced_hasDerivAt_zero.deriv]
  have hn : (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
  have he : star (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*
        ((canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) /
          (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)^2) =
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
    field_simp
  rw [he, Complex.ofReal_re]

theorem material_residual_core_center_pos : 0 < carryMaterialResidualCore 0 0 := by
  rw [material_residual_core_center]
  have h := reducedSourceScale_pos
  rw [reducedSourceScale_eq, sourceScale_eq] at h
  rcases div_pos_iff.mp h with h | h
  · exact h.1
  · exact False.elim ((not_lt_of_ge (sq_nonneg _)) h.2)

/-- Source-derived asymptotic positivity for every FIXED finite material
family with nonzero first moment. The small neighborhood depends on the
family. No uniform radius in c, n or direction is asserted. -/
theorem material_residual_fixed_family_positive {n : ℕ} (c t : Fin n → ℝ)
    (hm : (∑ i, c i*t i) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*t i) := by
  exact carryMaterialResidual_fixed_family_pos material_normalized_response_zero
    material_axis_continuous material_reduced_zero material_reduced_hasDerivAt_zero.differentiableAt
    material_reduced_deriv_continuous material_residual_core_center_pos c t hm

theorem material_residual_rescaled_energy_limit {n : ℕ} (c t : Fin n → ℝ) :
    Tendsto (carryMaterialRescaledResidualEnergy c t) (nhds 0)
      (nhds (canonicalCompletedNativeLogDerivativeMoment 1*(∑ i, c i*t i)^2)) := by
  have hc := carryMaterialRescaledResidualEnergy_continuous material_axis_continuous
    material_reduced_zero material_reduced_hasDerivAt_zero.differentiableAt
    material_reduced_deriv_continuous c t
  have hh := hc.tendsto
  rw [carryMaterialRescaledResidualEnergy_zero, material_residual_core_center] at hh
  exact hh

end
end CarryMaterialPositiveResidualComparison

namespace CarryMaterialPositiveResidualComparison
#assert_central_comparison_axioms material_real_kernel_coe
#print axioms material_real_kernel_coe
#assert_central_comparison_axioms material_real_residual_coe
#print axioms material_real_residual_coe
#assert_central_comparison_axioms material_real_feature_coe
#print axioms material_real_feature_coe
#assert_central_comparison_axioms material_real_feature_zero
#print axioms material_real_feature_zero
#assert_central_comparison_axioms material_real_feature_zero_pos
#print axioms material_real_feature_zero_pos
#assert_central_comparison_axioms material_real_residual_zero_left
#print axioms material_real_residual_zero_left
#assert_central_comparison_axioms material_real_residual_zero_right
#print axioms material_real_residual_zero_right
#assert_central_comparison_axioms material_real_kernel_split
#print axioms material_real_kernel_split
#assert_central_comparison_axioms material_centered_test_energy
#print axioms material_centered_test_energy
#assert_central_comparison_axioms material_full_residual_nonnegative_iff
#print axioms material_full_residual_nonnegative_iff
#assert_central_comparison_axioms material_extract_residual_of_full_realization
#print axioms material_extract_residual_of_full_realization
#assert_central_comparison_axioms material_lift_full_of_residual_realization
#print axioms material_lift_full_of_residual_realization
#assert_central_comparison_axioms material_residual_realization_center_zero
#print axioms material_residual_realization_center_zero
#assert_central_comparison_axioms material_residual_not_raw_reduced_pair_energy
#print axioms material_residual_not_raw_reduced_pair_energy
#assert_central_comparison_axioms material_axis_continuous
#print axioms material_axis_continuous
#assert_central_comparison_axioms material_residual_core_center
#print axioms material_residual_core_center
#assert_central_comparison_axioms material_residual_core_center_pos
#print axioms material_residual_core_center_pos
#assert_central_comparison_axioms material_residual_fixed_family_positive
#print axioms material_residual_fixed_family_positive
#assert_central_comparison_axioms material_residual_rescaled_energy_limit
#print axioms material_residual_rescaled_energy_limit
end CarryMaterialPositiveResidualComparison

-- Two genuinely noncentral material readings, with all ordered crosses.
namespace CarryMaterialPositiveResidualComparison
example : ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
    0 < GeometryOfNumbers.Analysis.carryRealKernelEnergy
      GeometryOfNumbers.Analysis.carryMaterialRealResidual ![1,-1]
      (fun i : Fin 2 => e*(![1,-1] : Fin 2 → ℝ) i) := by
  apply material_residual_fixed_family_positive ![1,-1] ![1,-1]
  norm_num [Fin.sum_univ_two]
end CarryMaterialPositiveResidualComparison

namespace CarryMaterialSecondNullComparison
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator CarrySelfAdjointOperator.SourcePositiveReduction
open CarryMaterialResponseComparison CarryMaterialResidualComparison CarryMaterialPositiveResidualComparison
open Filter
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem material_second_axis_eventually_eq :
    carryMaterialSecondAxis =ᶠ[nhds 0] fun t : ℝ => secondAxis (t : ℂ) :=
  CarryMaterialResidualComparison.real_dslope_germ material_reduced_eventually_eq
    reducedResponse_analyticAt_zero.differentiableAt

theorem material_second_axis_zero :
    carryMaterialSecondAxis 0 = (reducedSourceScale : ℂ) := by
  have h := material_second_axis_eventually_eq.eq_of_nhds
  simpa only [Complex.ofReal_zero, secondAxis_zero] using h

theorem material_second_scale_eq : carryMaterialSecondScale = reducedSourceScale := by
  rw [carryMaterialSecondScale, material_second_axis_zero, Complex.ofReal_re]

theorem material_second_scale_pos : 0 < carryMaterialSecondScale := by
  rw [material_second_scale_eq]
  exact reducedSourceScale_pos

theorem material_second_reduced_eventually_eq :
    carryMaterialSecondReducedResponse =ᶠ[nhds 0] fun t : ℝ => secondReducedResponse (t : ℂ) := by
  have hd := CarryMaterialResidualComparison.real_dslope_germ material_second_axis_eventually_eq
    secondAxis_analyticAt_zero.differentiableAt
  filter_upwards [hd, material_second_axis_eventually_eq] with t ht ha
  simp only [carryMaterialSecondReducedResponse, secondReducedResponse, ht, ha,
    material_second_scale_eq]

theorem material_second_reduced_zero : carryMaterialSecondReducedResponse 0 = 0 := by
  have h := material_second_reduced_eventually_eq.eq_of_nhds
  simpa only [Complex.ofReal_zero, secondReducedResponse_zero] using h

theorem material_second_reduced_hasDerivAt_zero :
    HasDerivAt carryMaterialSecondReducedResponse
      ((sourceScale*(sourceScale*canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1^2) /
          canonicalCompletedNativeLogDerivativeMoment 1^2 : ℝ) : ℂ) 0 :=
  secondReducedResponse_hasDerivAt_zero.comp_ofReal.congr_of_eventuallyEq
    material_second_reduced_eventually_eq

theorem material_second_reduced_deriv_continuous :
    ContinuousAt (deriv carryMaterialSecondReducedResponse) 0 := by
  have he := CarryMaterialResidualComparison.deriv_real_germ
    material_second_reduced_eventually_eq secondReducedResponse_analyticAt_zero
  have hco : ContinuousAt (fun t : ℝ => (t : ℂ)) 0 := Complex.continuous_ofReal.continuousAt
  have hcd : ContinuousAt (deriv secondReducedResponse) ((0 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_zero] using secondReducedResponse_analyticAt_zero.deriv.continuousAt
  exact (hcd.comp' hco).congr he.symm

theorem material_second_axis_conj (t : ℝ) : conj (carryMaterialSecondAxis t) = carryMaterialSecondAxis t :=
  CarryMaterialPositiveResidualComparison.real_dslope_conj _ material_reduced_conj 0 t

theorem material_second_reduced_conj (t : ℝ) :
    conj (carryMaterialSecondReducedResponse t) = carryMaterialSecondReducedResponse t := by
  have hd := CarryMaterialPositiveResidualComparison.real_dslope_conj _ material_second_axis_conj 0 t
  simp only [carryMaterialSecondReducedResponse, map_div₀, map_mul, hd,
    Complex.conj_ofReal, material_second_axis_conj]

theorem material_second_axis_hasDerivAt_zero : HasDerivAt carryMaterialSecondAxis 0 0 := by
  have h := secondAxis_analyticAt_zero.differentiableAt.hasDerivAt
  rw [deriv_secondAxis_zero] at h
  exact h.comp_ofReal.congr_of_eventuallyEq material_second_axis_eventually_eq

theorem material_second_channelCore_hasDerivAt_zero : HasDerivAt carryMaterialSecondChannelCore 0 0 := by
  have ha := sourceAxis_analyticAt_zero.differentiableAt.hasDerivAt
  have hb := secondAxis_analyticAt_zero.differentiableAt.hasDerivAt
  rw [deriv_sourceAxis_zero] at ha
  rw [deriv_secondAxis_zero] at hb
  have h := (ha.mul hb).div_const (Real.sqrt reducedSourceScale : ℂ)
  have hh : HasDerivAt (fun z : ℂ => sourceAxis z*secondAxis z /
      (Real.sqrt reducedSourceScale : ℂ)) 0 0 := by
    simpa only [zero_mul, mul_zero, add_zero, zero_div, Pi.mul_apply] using h
  have he : carryMaterialSecondChannelCore =ᶠ[nhds 0] fun t : ℝ =>
      sourceAxis (t : ℂ)*secondAxis (t : ℂ)/(Real.sqrt reducedSourceScale : ℂ) := by
    filter_upwards [material_axis_eventually_eq, material_second_axis_eventually_eq] with t ht hu
    simp only [carryMaterialSecondChannelCore, carryMaterialSecondAmplitudeCore, ht, hu,
      material_second_scale_eq]
  exact hh.comp_ofReal.congr_of_eventuallyEq he

theorem material_second_amplitude_continuous : ContinuousAt carryMaterialSecondAmplitudeCore 0 :=
  material_axis_continuous.mul material_second_axis_hasDerivAt_zero.continuousAt

private theorem second_positive_feature_germ :
    (fun t : ℝ => carryMaterialSecondAxis t/(Real.sqrt carryMaterialSecondScale : ℂ)) =ᶠ[nhds 0]
      fun t : ℝ => secondPositiveFeature (t : ℂ) := by
  filter_upwards [material_second_axis_eventually_eq] with t ht
  simp only [secondPositiveFeature, ht, material_second_scale_eq]

/-- Same existing second source reduction, extended to every local real
collision using only the scalar regularity supplied by the source. -/
theorem material_second_real_kernel_split :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U,
        dslope carryMaterialReducedResponse t u =
          inner ℂ (carryMaterialSecondAxis t/(Real.sqrt carryMaterialSecondScale : ℂ))
            (carryMaterialSecondAxis u/(Real.sqrt carryMaterialSecondScale : ℂ)) +
          conj (carryMaterialReducedResponse t)*carryMaterialReducedResponse u*
            dslope carryMaterialSecondReducedResponse t u := by
  have hphi : AnalyticAt ℂ secondPositiveFeature 0 :=
    secondAxis_analyticAt_zero.div analyticAt_const
      (by exact_mod_cast (Real.sqrt_pos.mpr reducedSourceScale_pos).ne')
  have hr := CarryMaterialResidualComparison.real_regular_germ material_reduced_eventually_eq
    reducedResponse_analyticAt_zero
  have hs := CarryMaterialResidualComparison.real_regular_germ material_second_reduced_eventually_eq
    secondReducedResponse_analyticAt_zero
  have hp := CarryMaterialResidualComparison.real_regular_germ second_positive_feature_germ hphi
  have hn : ∀ᶠ t : ℝ in nhds 0, secondAxis (t : ℂ) ≠ 0 := by
    have hne : secondAxis (0 : ℂ) ≠ 0 := by
      rw [secondAxis_zero]
      exact Complex.ofReal_ne_zero.mpr reducedSourceScale_pos.ne'
    have h := secondAxis_analyticAt_zero.continuousAt.eventually_ne hne
    exact CarryMaterialResidualComparison.real_cast_tendsto.eventually h
  have hall := material_reduced_eventually_eq.and (material_second_reduced_eventually_eq.and
    (second_positive_feature_germ.and (hn.and (hr.and (hs.and hp)))))
  rcases mem_nhds_iff.mp hall with ⟨U, hU, ho, hz⟩
  have hoff (t : ℝ) (ht : t ∈ U) (u : ℝ) (hu : u ∈ U) (hne : u ≠ t) :
      dslope carryMaterialReducedResponse t u =
        inner ℂ (carryMaterialSecondAxis t/(Real.sqrt carryMaterialSecondScale : ℂ))
          (carryMaterialSecondAxis u/(Real.sqrt carryMaterialSecondScale : ℂ)) +
        conj (carryMaterialReducedResponse t)*carryMaterialReducedResponse u*
          dslope carryMaterialSecondReducedResponse t u := by
    have htq := hU ht
    have huq := hU hu
    have hsep : (u : ℂ) ≠ conj (t : ℂ) := by simpa using hne
    have h := reducedKernel_split (t : ℂ) (u : ℂ) htq.2.2.2.1 huq.2.2.2.1 hsep
    rw [CarryMaterialResidualComparison.real_dslope_offdiag _ hne,
      CarryMaterialResidualComparison.real_dslope_offdiag _ hne]
    have hrt : carryMaterialReducedResponse t = reducedResponse (t : ℂ) := htq.1
    have hru : carryMaterialReducedResponse u = reducedResponse (u : ℂ) := huq.1
    have hst : carryMaterialSecondReducedResponse t = secondReducedResponse (t : ℂ) := htq.2.1
    have hsu : carryMaterialSecondReducedResponse u = secondReducedResponse (u : ℂ) := huq.2.1
    have hpt : carryMaterialSecondAxis t/(Real.sqrt carryMaterialSecondScale : ℂ) =
        secondPositiveFeature (t : ℂ) := htq.2.2.1
    have hpu : carryMaterialSecondAxis u/(Real.sqrt carryMaterialSecondScale : ℂ) =
        secondPositiveFeature (u : ℂ) := huq.2.2.1
    rw [reducedKernel, secondReducedKernel, ← hrt, ← hru, ← hst, ← hsu, ← hpt, ← hpu,
      material_reduced_conj, material_second_reduced_conj, Complex.conj_ofReal] at h
    simpa only [material_reduced_conj] using h
  refine ⟨U, ho, hz, ?_⟩
  intro t ht u hu
  by_cases hne : u ≠ t
  · exact hoff t ht u hu hne
  · have he : u = t := not_ne_iff.mp hne
    subst u
    have hreg := (hU ht).2.2.2.2
    have hl : ContinuousAt (dslope carryMaterialReducedResponse t) t :=
      continuousAt_dslope_same.mpr hreg.1.differentiableAt
    have hd : ContinuousAt (dslope carryMaterialSecondReducedResponse t) t :=
      continuousAt_dslope_same.mpr hreg.2.1.differentiableAt
    have hph := hreg.2.2.continuousAt
    have hc : ContinuousAt (fun u : ℝ =>
        inner ℂ (carryMaterialSecondAxis t/(Real.sqrt carryMaterialSecondScale : ℂ))
          (carryMaterialSecondAxis u/(Real.sqrt carryMaterialSecondScale : ℂ)) +
        conj (carryMaterialReducedResponse t)*carryMaterialReducedResponse u*
          dslope carryMaterialSecondReducedResponse t u) t := by
      apply ContinuousAt.add
      · have hh := hph.mul (show ContinuousAt (fun _ : ℝ =>
          conj (carryMaterialSecondAxis t/(Real.sqrt carryMaterialSecondScale : ℂ))) t from continuousAt_const)
        change ContinuousAt (fun u : ℝ =>
          carryMaterialSecondAxis u/(Real.sqrt carryMaterialSecondScale : ℂ)*
            conj (carryMaterialSecondAxis t/(Real.sqrt carryMaterialSecondScale : ℂ))) t at hh
        simpa only [RCLike.inner_apply] using hh
      · exact (continuousAt_const.mul hreg.1.continuousAt).mul hd
    have heq : dslope carryMaterialReducedResponse t =ᶠ[nhdsWithin t {t}ᶜ]
        (fun u => inner ℂ (carryMaterialSecondAxis t/(Real.sqrt carryMaterialSecondScale : ℂ))
          (carryMaterialSecondAxis u/(Real.sqrt carryMaterialSecondScale : ℂ)) +
        conj (carryMaterialReducedResponse t)*carryMaterialReducedResponse u*
          dslope carryMaterialSecondReducedResponse t u) := by
      have hm : ∀ᶠ u : ℝ in nhds t, u ∈ U := ho.mem_nhds ht
      filter_upwards [self_mem_nhdsWithin, hm.filter_mono nhdsWithin_le_nhds] with u hne hu
      exact hoff t ht u hu (by simpa using hne)
    exact tendsto_nhds_unique ((hl.tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
      (hc.tendsto.mono_left nhdsWithin_le_nhds)

/-- The same normalized residual as PR #8/#9, with the next extracted
channel and the ENTIRE second reduced response, including all diagonals. -/
theorem material_second_residual_split :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U, carryMaterialRealResidual t u =
        (conj (carryMaterialSecondPositiveChannel t)*carryMaterialSecondPositiveChannel u).re +
          t^2*u^2*carryMaterialSecondResidualCore t u := by
  rcases material_second_real_kernel_split with ⟨U, ho, hz, h⟩
  refine ⟨U, ho, hz, ?_⟩
  intro t ht u hu
  have he : conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse u*
      dslope carryMaterialReducedResponse t u =
      conj (carryMaterialSecondPositiveChannel t)*carryMaterialSecondPositiveChannel u +
        ((t^2*u^2 : ℝ) : ℂ)*
          (conj (carryMaterialSecondAmplitudeCore t)*carryMaterialSecondAmplitudeCore u*
            dslope carryMaterialSecondReducedResponse t u) := by
    rw [h t ht u hu]
    have htamp := carryMaterialSecondAmplitude_factor material_normalized_response_zero material_reduced_zero t
    have huamp := carryMaterialSecondAmplitude_factor material_normalized_response_zero material_reduced_zero u
    have hh : conj (carryMaterialNormalizedResponse t*carryMaterialReducedResponse t)*
        (carryMaterialNormalizedResponse u*carryMaterialReducedResponse u)*
          dslope carryMaterialSecondReducedResponse t u =
      ((t^2*u^2 : ℝ) : ℂ)*
        (conj (carryMaterialSecondAmplitudeCore t)*carryMaterialSecondAmplitudeCore u*
          dslope carryMaterialSecondReducedResponse t u) := by
      rw [htamp, huamp]
      simp only [map_mul, map_pow, Complex.conj_ofReal]
      push_cast
      ring
    simp only [map_mul] at hh
    simp only [carryMaterialSecondPositiveChannel, RCLike.inner_apply, map_div₀, map_mul]
    linear_combination hh
  have hr := congrArg Complex.re he
  simpa only [carryMaterialRealResidual, carryMaterialSecondResidualCore, Complex.star_def,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] using hr

/-- The source discriminant, not an assigned positive metric. -/
theorem material_second_residual_core_center :
    carryMaterialSecondResidualCore 0 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1^2) /
          canonicalCompletedNativeLogDerivativeMoment 0 := by
  unfold carryMaterialSecondResidualCore carryMaterialSecondAmplitudeCore
  rw [material_axis_zero, material_second_axis_zero, dslope_same,
    material_second_reduced_hasDerivAt_zero.deriv, reducedSourceScale_eq, sourceScale_eq]
  have h0 : (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
  have h1 : (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ) ≠ 0 := by
    have hp : 0 < canonicalCompletedNativeLogDerivativeMoment 1 := by
      simpa only [material_residual_core_center] using material_residual_core_center_pos
    exact Complex.ofReal_ne_zero.mpr hp.ne'
  have he :
      conj ((canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*
        ((canonicalCompletedNativeLogDerivativeMoment 1 /
          canonicalCompletedNativeLogDerivativeMoment 0^2 : ℝ) : ℂ)) *
      ((canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*
        ((canonicalCompletedNativeLogDerivativeMoment 1 /
          canonicalCompletedNativeLogDerivativeMoment 0^2 : ℝ) : ℂ)) *
      ((canonicalCompletedNativeLogDerivativeMoment 0 *
        (canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2 -
          canonicalCompletedNativeLogDerivativeMoment 1^2) /
          canonicalCompletedNativeLogDerivativeMoment 1^2 : ℝ) : ℂ) =
      (((canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1^2) /
          canonicalCompletedNativeLogDerivativeMoment 0 : ℝ) : ℂ) := by
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    field_simp [h0, h1]
  rw [he, Complex.ofReal_re]

theorem material_second_residual_core_center_pos : 0 < carryMaterialSecondResidualCore 0 0 := by
  have hd := nativeSourceMixedDiscriminants_pos.1
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical] at hd
  have hdelta : 0 < canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2 -
      canonicalCompletedNativeLogDerivativeMoment 1^2 := by nlinarith
  rw [material_second_residual_core_center]
  exact div_pos hdelta canonicalCompletedNativeLogDerivativeMoment_zero_pos

/-- Exact fourth-order factorization for every fixed finite source family
that cancels the first moment. No moment-two condition is needed here. -/
theorem material_second_null_energy_factor {n : ℕ} (c a : Fin n → ℝ)
    (hc : (∑ i, c i*a i) = 0) :
    ∀ᶠ e : ℝ in nhds 0,
      carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) =
        e^4*carryMaterialSecondNullEnergy c a e := by
  rcases material_second_residual_split with ⟨U, ho, hz, h⟩
  have hm : ∀ᶠ e : ℝ in nhds 0, ∀ i, e*a i ∈ U := by
    apply Filter.eventually_all.mpr
    intro i
    have he : Tendsto (fun e : ℝ => e*a i) (nhds 0) (nhds 0) := by
      simpa only [id_eq, zero_mul] using (continuousAt_id.mul_const (a i)).tendsto (x := (0 : ℝ))
    exact he.eventually (ho.mem_nhds hz)
  filter_upwards [hm] with e he
  exact carryMaterialSecondNull_energy_factor h material_normalized_response_zero c a hc e he

/-- All finite ordered crossings survive in the rescaled limit. -/
theorem material_second_null_energy_limit {n : ℕ} (c a : Fin n → ℝ) :
    Tendsto (carryMaterialSecondNullEnergy c a) (nhds 0)
      (nhds (((canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1^2) /
          canonicalCompletedNativeLogDerivativeMoment 0)*(∑ i, c i*(a i)^2)^2)) := by
  have h := carryMaterialSecondNullEnergy_continuous material_second_amplitude_continuous
    material_second_channelCore_hasDerivAt_zero.differentiableAt material_second_reduced_zero
    material_second_reduced_hasDerivAt_zero.differentiableAt material_second_reduced_deriv_continuous c a
  have ht := h.tendsto
  rw [carryMaterialSecondNullEnergy_zero material_second_channelCore_hasDerivAt_zero.deriv,
    material_second_residual_core_center] at ht
  exact ht

/-- Positive for any FIXED family with M1=0 and M2!=0, at sufficiently
small nonzero scales. No uniform neighborhood over families is claimed. -/
theorem material_second_null_fixed_family_positive {n : ℕ} (c a : Fin n → ℝ)
    (hc : (∑ i, c i*a i) = 0) (hm : (∑ i, c i*(a i)^2) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) := by
  rcases material_second_residual_split with ⟨U, ho, hz, h⟩
  exact carryMaterialSecondNull_fixed_family_pos (ho.mem_nhds hz) h
    material_normalized_response_zero material_second_amplitude_continuous
    material_second_channelCore_hasDerivAt_zero.differentiableAt
    material_second_channelCore_hasDerivAt_zero.deriv material_second_reduced_zero
    material_second_reduced_hasDerivAt_zero.differentiableAt material_second_reduced_deriv_continuous
    material_second_residual_core_center_pos c a hc hm

/-- Explicit local lower margin for the complete residual energy. The
radius depends on the fixed family; the source coefficient is unchanged. -/
theorem material_second_null_energy_lower_bound {n : ℕ} (c a : Fin n → ℝ)
    (hc : (∑ i, c i*a i) = 0) (hm : (∑ i, c i*(a i)^2) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0,
      (((canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2 -
        canonicalCompletedNativeLogDerivativeMoment 1^2) /
          canonicalCompletedNativeLogDerivativeMoment 0)*(∑ i, c i*(a i)^2)^2)/2*e^4 ≤
        carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) := by
  let C : ℝ := ((canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2 -
      canonicalCompletedNativeLogDerivativeMoment 1^2) /
        canonicalCompletedNativeLogDerivativeMoment 0)*(∑ i, c i*(a i)^2)^2
  have hC : 0 < C := by
    have hp := material_second_residual_core_center_pos
    rw [material_second_residual_core_center] at hp
    exact mul_pos hp (sq_pos_of_ne_zero hm)
  have hlim : Tendsto (carryMaterialSecondNullEnergy c a) (nhds 0) (nhds C) :=
    material_second_null_energy_limit c a
  have hmargin : ∀ᶠ e : ℝ in nhds 0, C/2 < carryMaterialSecondNullEnergy c a e :=
    (tendsto_order.1 hlim).1 (C/2) (by linarith)
  filter_upwards [hmargin, material_second_null_energy_factor c a hc] with e he hfactor
  change C/2*e^4 ≤ _
  rw [hfactor, mul_comm (C/2)]
  exact mul_le_mul_of_nonneg_left he.le (by positivity)

end
end CarryMaterialSecondNullComparison

namespace CarryMaterialSecondNullComparison
#assert_central_comparison_axioms material_second_axis_eventually_eq
#print axioms material_second_axis_eventually_eq
#assert_central_comparison_axioms material_second_axis_zero
#print axioms material_second_axis_zero
#assert_central_comparison_axioms material_second_scale_eq
#print axioms material_second_scale_eq
#assert_central_comparison_axioms material_second_scale_pos
#print axioms material_second_scale_pos
#assert_central_comparison_axioms material_second_reduced_eventually_eq
#print axioms material_second_reduced_eventually_eq
#assert_central_comparison_axioms material_second_reduced_zero
#print axioms material_second_reduced_zero
#assert_central_comparison_axioms material_second_reduced_hasDerivAt_zero
#print axioms material_second_reduced_hasDerivAt_zero
#assert_central_comparison_axioms material_second_reduced_deriv_continuous
#print axioms material_second_reduced_deriv_continuous
#assert_central_comparison_axioms material_second_axis_conj
#print axioms material_second_axis_conj
#assert_central_comparison_axioms material_second_reduced_conj
#print axioms material_second_reduced_conj
#assert_central_comparison_axioms material_second_axis_hasDerivAt_zero
#print axioms material_second_axis_hasDerivAt_zero
#assert_central_comparison_axioms material_second_channelCore_hasDerivAt_zero
#print axioms material_second_channelCore_hasDerivAt_zero
#assert_central_comparison_axioms material_second_amplitude_continuous
#print axioms material_second_amplitude_continuous
#assert_central_comparison_axioms material_second_real_kernel_split
#print axioms material_second_real_kernel_split
#assert_central_comparison_axioms material_second_residual_split
#print axioms material_second_residual_split
#assert_central_comparison_axioms material_second_residual_core_center
#print axioms material_second_residual_core_center
#assert_central_comparison_axioms material_second_residual_core_center_pos
#print axioms material_second_residual_core_center_pos
#assert_central_comparison_axioms material_second_null_energy_factor
#print axioms material_second_null_energy_factor
#assert_central_comparison_axioms material_second_null_energy_limit
#print axioms material_second_null_energy_limit
#assert_central_comparison_axioms material_second_null_fixed_family_positive
#print axioms material_second_null_fixed_family_positive
#assert_central_comparison_axioms material_second_null_energy_lower_bound
#print axioms material_second_null_energy_lower_bound
end CarryMaterialSecondNullComparison

namespace CarryMaterialSecondNullComparison
open GeometryOfNumbers.Analysis Filter
open scoped BigOperators Topology
set_option autoImplicit false
-- This is exactly the reflection combination whose leading form vanished in PR #9.
example : ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
    0 < carryRealKernelEnergy carryMaterialRealResidual (![1,1] : Fin 2 → ℝ)
      (fun i => e*(![1,-1] : Fin 2 → ℝ) i) := by
  apply material_second_null_fixed_family_positive ![1,1] ![1,-1]
  · norm_num [Fin.sum_univ_two]
  · norm_num [Fin.sum_univ_two]

-- A genuine three-reading double cancellation stays outside the new sign theorem.
example : Tendsto (carryMaterialSecondNullEnergy (![3,-3,1] : Fin 3 → ℝ) ![1,2,3])
    (nhds 0) (nhds 0) := by
  have h := material_second_null_energy_limit (![3,-3,1] : Fin 3 → ℝ) ![1,2,3]
  norm_num [Fin.sum_univ_three,
    show (![3,-3,1] : Fin 3 → ℝ) 2 = 1 from rfl,
    show (![1,2,3] : Fin 3 → ℝ) 2 = 3 from rfl] at h
  exact h
end CarryMaterialSecondNullComparison

namespace CarryMaterialThirdNullComparison
open GeometryOfNumbers.Analysis Filter
open CarrySelfAdjointOperator CarrySelfAdjointOperator.SourcePositiveReduction
open CarryMaterialResponseComparison CarryMaterialResidualComparison
open CarryMaterialPositiveResidualComparison
open scoped BigOperators Topology ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

private def nativeTaylorShift (n : ℕ) : ℂ → ℂ :=
  (Function.swap dslope (0 : ℂ))^[n] sourceResponse

private theorem nativeTaylorShift_analytic (n : ℕ) : AnalyticAt ℂ (nativeTaylorShift n) 0 := by
  rcases sourceResponse_analyticAt_zero with ⟨p, hp⟩
  exact (hp.has_fpower_series_iterate_dslope_fslope n).analyticAt

private theorem source_series_coeff {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt sourceResponse p 0) (n : ℕ) :
    p.coeff n = completedNativeGreenResponseTaylorCoefficient n := by
  have he : p.coeff n = completedGreenTaylorJet sourceResponse n := by
    rcases hp with ⟨radius, hball⟩
    have hd := hball.factorial_smul (1 : ℂ) n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod] at hd
    simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const_one, one_smul] at hd
    have h : (n.factorial : ℂ) • p.coeff n = iteratedDeriv n sourceResponse 0 := by
      simpa only [Nat.cast_smul_eq_nsmul] using hd
    rw [completedGreenTaylorJet, ← h, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_smul]
  exact he.trans (sourceResponse_taylor n)

/-- Every material Taylor shift is a germ of the SAME analytic scalar source. -/
theorem material_taylor_shift_germ (n : ℕ) :
    carryMaterialTaylorShift n =ᶠ[nhds 0] fun t : ℝ => nativeTaylorShift n (t : ℂ) := by
  induction n with
  | zero => exact material_source_response_eventually_eq
  | succ n ih =>
    have h := CarryMaterialResidualComparison.real_dslope_germ ih
      (nativeTaylorShift_analytic n).differentiableAt
    simpa only [carryMaterialTaylorShift_succ, nativeTaylorShift,
      Function.iterate_succ_apply'] using h

theorem material_taylor_shift_center (n : ℕ) :
    carryMaterialTaylorShift n 0 = completedNativeGreenResponseTaylorCoefficient n := by
  rcases sourceResponse_analyticAt_zero with ⟨p, hp⟩
  have hs := hp.has_fpower_series_iterate_dslope_fslope n
  have hc : nativeTaylorShift n 0 = p.coeff n := by
    have h := hs.coeff_zero 1
    change (FormalMultilinearSeries.fslope^[n] p).coeff 0 = nativeTaylorShift n 0 at h
    rw [FormalMultilinearSeries.coeff_iterate_fslope, zero_add] at h
    exact h.symm
  simpa only [Complex.ofReal_zero, hc, source_series_coeff hp] using
    (material_taylor_shift_germ n).eq_of_nhds

theorem material_taylor_shift_hasDerivAt_zero (n : ℕ) :
    HasDerivAt (carryMaterialTaylorShift n)
      (completedNativeGreenResponseTaylorCoefficient (n+1)) 0 := by
  rcases sourceResponse_analyticAt_zero with ⟨p, hp⟩
  have hs := hp.has_fpower_series_iterate_dslope_fslope n
  have hd := hs.analyticAt.differentiableAt.hasDerivAt
  rw [hs.deriv] at hd
  change HasDerivAt (nativeTaylorShift n) ((FormalMultilinearSeries.fslope^[n] p).coeff 1) 0 at hd
  rw [FormalMultilinearSeries.coeff_iterate_fslope, source_series_coeff hp] at hd
  have he : HasDerivAt (nativeTaylorShift n)
      (completedNativeGreenResponseTaylorCoefficient (n+1)) 0 := by
    simpa only [Nat.add_comm] using hd
  exact he.comp_ofReal.congr_of_eventuallyEq (material_taylor_shift_germ n)

theorem material_taylor_shift_regular (n : ℕ) :
    ∀ᶠ t : ℝ in nhds 0, DifferentiableAt ℝ (carryMaterialTaylorShift n) t := by
  filter_upwards [CarryMaterialResidualComparison.real_regular_germ
    (material_taylor_shift_germ n) (nativeTaylorShift_analytic n)] with t ht
  exact ht.differentiableAt

theorem material_taylor_shift_deriv_continuous (n : ℕ) :
    ContinuousAt (deriv (carryMaterialTaylorShift n)) 0 := by
  have he := CarryMaterialResidualComparison.deriv_real_germ
    (material_taylor_shift_germ n) (nativeTaylorShift_analytic n)
  have hco : ContinuousAt (fun t : ℝ => (t : ℂ)) 0 := Complex.continuous_ofReal.continuousAt
  have hcd : ContinuousAt (deriv (nativeTaylorShift n)) ((0 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_zero] using (nativeTaylorShift_analytic n).deriv.continuousAt
  exact (hcd.comp' hco).congr he.symm

theorem material_taylor_shift_conj (n : ℕ) (t : ℝ) :
    conj (carryMaterialTaylorShift n t) = carryMaterialTaylorShift n t :=
  carryMaterialTaylorShift_conj material_response_conj n t

theorem material_second_taylor_shift_zero : carryMaterialTaylorShift 2 0 = 0 := by
  rw [material_taylor_shift_center]
  exact completedNativeGreenResponseTaylorCoefficient_even_eq_zero 1

theorem material_fourth_taylor_shift_zero : carryMaterialTaylorShift 4 0 = 0 := by
  rw [material_taylor_shift_center]
  exact completedNativeGreenResponseTaylorCoefficient_even_eq_zero 2

theorem material_sixth_taylor_shift_zero : carryMaterialTaylorShift 6 0 = 0 := by
  rw [material_taylor_shift_center]
  exact completedNativeGreenResponseTaylorCoefficient_even_eq_zero 3

theorem material_sixth_taylor_shift_hasDerivAt_zero :
    HasDerivAt (carryMaterialTaylorShift 6) (canonicalCompletedNativeLogDerivativeMoment 3 : ℂ) 0 := by
  have h := material_taylor_shift_hasDerivAt_zero 6
  rw [show 6+1=2*3+1 from rfl,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical] at h
  exact h

theorem material_moment_three_pos : 0 < canonicalCompletedNativeLogDerivativeMoment 3 := by
  have h1 := nativeMoment_one_pos
  have hdelta := nativeMoment_shifted_discriminant_pos
  by_contra h
  have hn := mul_nonpos_of_nonneg_of_nonpos h1.le (le_of_not_gt h)
  nlinarith [sq_nonneg (canonicalCompletedNativeLogDerivativeMoment 2)]

/-- The already identified source split, with its literal central normalization. -/
theorem material_residual_centered_kernel :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧
      ∀ t ∈ U, ∀ u ∈ U, (carryMaterialRealResidual t u : ℂ) =
        dslope carryMaterialNormalizedResponse t u-
          carryMaterialTaylorShift 1 t*carryMaterialTaylorShift 1 u /
            (carryMaterialResponseScale : ℂ) := by
  rcases CarryMaterialResidualComparison.material_real_kernel_split with ⟨U, ho, hz, hs⟩
  have hphi (t u : ℝ) : inner ℂ (carryMaterialPositiveFeature t) (carryMaterialPositiveFeature u) =
      carryMaterialTaylorShift 1 t*carryMaterialTaylorShift 1 u /
        (carryMaterialResponseScale : ℂ) := by
    have hsq : (Real.sqrt carryMaterialResponseScale : ℂ)^2 = (carryMaterialResponseScale : ℂ) := by
      exact_mod_cast Real.sq_sqrt material_scale_pos.le
    simp only [carryMaterialPositiveFeature, RCLike.inner_apply, map_div₀,
      Complex.conj_ofReal, material_axis_conj]
    rw [div_mul_div_comm, ← pow_two, hsq]
    change carryMaterialResponseAxis u*carryMaterialResponseAxis t / _ = _
    change _ = carryMaterialResponseAxis t*carryMaterialResponseAxis u / _
    ring
  refine ⟨U, ho, hz, ?_⟩
  intro t ht u hu
  have h := hs t ht u hu
  rw [hphi] at h
  rw [material_real_residual_coe]
  linear_combination -h

theorem material_third_null_energy_factor {n : ℕ} (c a : Fin n → ℝ)
    (hM1 : (∑ i, c i*a i) = 0) (hM2 : (∑ i, c i*(a i)^2) = 0) :
    ∀ᶠ e : ℝ in nhds 0,
      carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) =
        e^6*carryMaterialThirdNullEnergy c a e := by
  rcases material_residual_centered_kernel with ⟨U, ho, hz, hs⟩
  have hscale : carryMaterialTaylorShift 1 0 = (carryMaterialResponseScale : ℂ) := by
    change carryMaterialResponseAxis 0 = _
    rw [material_axis_zero, material_scale_eq]
  have hm : ∀ᶠ e : ℝ in nhds 0, ∀ i, e*a i ∈ U := by
    apply Filter.eventually_all.mpr
    intro i
    have ht : Tendsto (fun e : ℝ => e*a i) (nhds 0) (nhds 0) := by
      simpa only [id_eq, zero_mul] using (continuousAt_id.mul_const (a i)).tendsto (x := (0 : ℝ))
    exact ht.eventually (ho.mem_nhds hz)
  have hreg (j : ℕ) : ∀ᶠ e : ℝ in nhds 0, ∀ i,
      DifferentiableAt ℝ (carryMaterialTaylorShift j) (e*a i) := by
    apply Filter.eventually_all.mpr
    intro i
    have ht : Tendsto (fun e : ℝ => e*a i) (nhds 0) (nhds 0) := by
      simpa only [id_eq, zero_mul] using (continuousAt_id.mul_const (a i)).tendsto (x := (0 : ℝ))
    exact ht.eventually (material_taylor_shift_regular j)
  filter_upwards [hm, hreg 2, hreg 4, hreg 6] with e he h2 h4 h6
  exact carryMaterialThirdNull_energy_factor hs hscale material_scale_pos
    material_second_taylor_shift_zero material_fourth_taylor_shift_zero
    (material_taylor_shift_conj 5) c a hM1 hM2 e he h2 h4 h6

theorem material_third_null_energy_continuous {n : ℕ} (c a : Fin n → ℝ) :
    ContinuousAt (carryMaterialThirdNullEnergy c a) 0 :=
  carryMaterialThirdNullEnergy_continuous
    (material_taylor_shift_hasDerivAt_zero 5).continuousAt material_sixth_taylor_shift_zero
    material_sixth_taylor_shift_hasDerivAt_zero.differentiableAt
    (material_taylor_shift_deriv_continuous 6) c a

/-- Central coefficient of the TOTAL residual, not only the newest channel. -/
theorem material_third_null_energy_limit {n : ℕ} (c a : Fin n → ℝ) :
    Tendsto (carryMaterialThirdNullEnergy c a) (nhds 0)
      (nhds (canonicalCompletedNativeLogDerivativeMoment 3*(∑ i, c i*(a i)^3)^2)) := by
  have h := (material_third_null_energy_continuous c a).tendsto
  rw [carryMaterialThirdNullEnergy_zero, material_sixth_taylor_shift_hasDerivAt_zero.deriv,
    Complex.ofReal_re] at h
  exact h

/-- The normalized quotient is used only on the punctured neighborhood. -/
theorem material_third_null_scaled_energy_limit {n : ℕ} (c a : Fin n → ℝ)
    (hM1 : (∑ i, c i*a i) = 0) (hM2 : (∑ i, c i*(a i)^2) = 0) :
    Tendsto (fun e : ℝ => carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i)/e^6)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (canonicalCompletedNativeLogDerivativeMoment 3*(∑ i, c i*(a i)^3)^2)) := by
  have heq : (fun e : ℝ => carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i)/e^6)
      =ᶠ[nhdsWithin 0 {0}ᶜ] carryMaterialThirdNullEnergy c a := by
    filter_upwards [self_mem_nhdsWithin,
      (material_third_null_energy_factor c a hM1 hM2).filter_mono nhdsWithin_le_nhds] with e hne hf
    have he : e ≠ 0 := by simpa using hne
    rw [hf]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ he)
  exact ((material_third_null_energy_limit c a).mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- Every FIXED family in the double-null sector with a nonzero third
material moment has positive complete residual energy at small nonzero scale. -/
theorem material_third_null_fixed_family_positive {n : ℕ} (c a : Fin n → ℝ)
    (hM1 : (∑ i, c i*a i) = 0) (hM2 : (∑ i, c i*(a i)^2) = 0)
    (hM3 : (∑ i, c i*(a i)^3) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) := by
  have hpos : 0 < canonicalCompletedNativeLogDerivativeMoment 3*(∑ i, c i*(a i)^3)^2 :=
    mul_pos material_moment_three_pos (sq_pos_of_ne_zero hM3)
  have hQ := (tendsto_order.1 (material_third_null_energy_limit c a)).1 0 hpos
  filter_upwards [hQ, material_third_null_energy_factor c a hM1 hM2] with e he hf hne
  rw [hf]
  have hp : 0 < e^6 := by
    simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero hne) 3
  exact mul_pos hp he

/-- A local margin for the full energy, with no change of normalization. -/
theorem material_third_null_energy_lower_bound {n : ℕ} (c a : Fin n → ℝ)
    (hM1 : (∑ i, c i*a i) = 0) (hM2 : (∑ i, c i*(a i)^2) = 0)
    (hM3 : (∑ i, c i*(a i)^3) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0,
      canonicalCompletedNativeLogDerivativeMoment 3*(∑ i, c i*(a i)^3)^2/2*e^6 ≤
        carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) := by
  let C : ℝ := canonicalCompletedNativeLogDerivativeMoment 3*(∑ i, c i*(a i)^3)^2
  have hC : 0 < C := mul_pos material_moment_three_pos (sq_pos_of_ne_zero hM3)
  have hlim : Tendsto (carryMaterialThirdNullEnergy c a) (nhds 0) (nhds C) :=
    material_third_null_energy_limit c a
  have hmargin : ∀ᶠ e : ℝ in nhds 0, C/2 < carryMaterialThirdNullEnergy c a e :=
    (tendsto_order.1 hlim).1 (C/2) (by linarith)
  filter_upwards [hmargin, material_third_null_energy_factor c a hM1 hM2] with e he hf
  change C/2*e^6 ≤ _
  rw [hf, mul_comm (C/2)]
  exact mul_le_mul_of_nonneg_left he.le (by positivity)

end
end CarryMaterialThirdNullComparison

namespace CarryMaterialThirdNullComparison
#assert_central_comparison_axioms material_taylor_shift_germ
#print axioms material_taylor_shift_germ
#assert_central_comparison_axioms material_taylor_shift_center
#print axioms material_taylor_shift_center
#assert_central_comparison_axioms material_taylor_shift_hasDerivAt_zero
#print axioms material_taylor_shift_hasDerivAt_zero
#assert_central_comparison_axioms material_taylor_shift_regular
#print axioms material_taylor_shift_regular
#assert_central_comparison_axioms material_taylor_shift_deriv_continuous
#print axioms material_taylor_shift_deriv_continuous
#assert_central_comparison_axioms material_taylor_shift_conj
#print axioms material_taylor_shift_conj
#assert_central_comparison_axioms material_second_taylor_shift_zero
#print axioms material_second_taylor_shift_zero
#assert_central_comparison_axioms material_fourth_taylor_shift_zero
#print axioms material_fourth_taylor_shift_zero
#assert_central_comparison_axioms material_sixth_taylor_shift_zero
#print axioms material_sixth_taylor_shift_zero
#assert_central_comparison_axioms material_sixth_taylor_shift_hasDerivAt_zero
#print axioms material_sixth_taylor_shift_hasDerivAt_zero
#assert_central_comparison_axioms material_moment_three_pos
#print axioms material_moment_three_pos
#assert_central_comparison_axioms material_residual_centered_kernel
#print axioms material_residual_centered_kernel
#assert_central_comparison_axioms material_third_null_energy_factor
#print axioms material_third_null_energy_factor
#assert_central_comparison_axioms material_third_null_energy_continuous
#print axioms material_third_null_energy_continuous
#assert_central_comparison_axioms material_third_null_energy_limit
#print axioms material_third_null_energy_limit
#assert_central_comparison_axioms material_third_null_scaled_energy_limit
#print axioms material_third_null_scaled_energy_limit
#assert_central_comparison_axioms material_third_null_fixed_family_positive
#print axioms material_third_null_fixed_family_positive
#assert_central_comparison_axioms material_third_null_energy_lower_bound
#print axioms material_third_null_energy_lower_bound
end CarryMaterialThirdNullComparison

namespace CarryMaterialThirdNullComparison
open GeometryOfNumbers.Analysis Filter CarrySelfAdjointOperator
open scoped BigOperators Topology

-- The genuinely double-cancelling three-reading source from PR #10 now has a sign.
example : ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
    0 < carryRealKernelEnergy carryMaterialRealResidual (![3,-3,1] : Fin 3 → ℝ)
      (fun i => e*(![1,2,3] : Fin 3 → ℝ) i) := by
  apply material_third_null_fixed_family_positive ![3,-3,1] ![1,2,3]
  · norm_num [Fin.sum_univ_three,
      show (![3,-3,1] : Fin 3 → ℝ) 2 = 1 from rfl,
      show (![1,2,3] : Fin 3 → ℝ) 2 = 3 from rfl]
  · norm_num [Fin.sum_univ_three,
      show (![3,-3,1] : Fin 3 → ℝ) 2 = 1 from rfl,
      show (![1,2,3] : Fin 3 → ℝ) 2 = 3 from rfl]
  · norm_num [Fin.sum_univ_three,
      show (![3,-3,1] : Fin 3 → ℝ) 2 = 1 from rfl,
      show (![1,2,3] : Fin 3 → ℝ) 2 = 3 from rfl]

example : Tendsto (carryMaterialThirdNullEnergy (![3,-3,1] : Fin 3 → ℝ) ![1,2,3])
    (nhds 0) (nhds (36*canonicalCompletedNativeLogDerivativeMoment 3)) := by
  have h := material_third_null_energy_limit (![3,-3,1] : Fin 3 → ℝ) ![1,2,3]
  norm_num [Fin.sum_univ_three,
    show (![3,-3,1] : Fin 3 → ℝ) 2 = 1 from rfl,
    show (![1,2,3] : Fin 3 → ℝ) 2 = 3 from rfl] at h
  simpa only [mul_comm] using h

-- Triple cancellation has zero sixth-order coefficient: no sign inferred.
example {n : ℕ} (c a : Fin n → ℝ) (hM3 : (∑ i, c i*(a i)^3) = 0) :
    Tendsto (carryMaterialThirdNullEnergy c a) (nhds 0) (nhds 0) := by
  simpa only [hM3, zero_pow (by decide : 2 ≠ 0), mul_zero] using
    material_third_null_energy_limit c a

end CarryMaterialThirdNullComparison

namespace CarryMaterialNullHierarchyComparison
open GeometryOfNumbers.Analysis Filter
open CarrySelfAdjointOperator CarrySelfAdjointOperator.SourcePositiveReduction
open CarryMaterialResponseComparison CarryMaterialResidualComparison
open CarryMaterialThirdNullComparison
open scoped BigOperators Topology ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Parity and derivative calibration use the already proved ALL-ORDER
Taylor provenance. They do not postulate the sign of any moment. -/
theorem material_even_taylor_shift_zero (k : ℕ) : carryMaterialTaylorShift (2*k) 0 = 0 := by
  rw [material_taylor_shift_center]
  exact completedNativeGreenResponseTaylorCoefficient_even_eq_zero k

theorem material_even_taylor_shift_hasDerivAt_zero (k : ℕ) :
    HasDerivAt (carryMaterialTaylorShift (2*k)) (canonicalCompletedNativeLogDerivativeMoment k : ℂ) 0 := by
  have h := material_taylor_shift_hasDerivAt_zero (2*k)
  rw [completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical] at h
  exact h

/-- Literal source coefficient, including the central-channel correction. -/
theorem material_null_coefficient_source (k : ℕ) :
    carryMaterialNullCoefficient k = canonicalCompletedNativeLogDerivativeMoment k -
      ‖completedNativeGreenResponseTaylorCoefficient (k+1)‖^2 /
        canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [carryMaterialNullCoefficient, (material_even_taylor_shift_hasDerivAt_zero k).deriv,
    Complex.ofReal_re, material_taylor_shift_center, material_scale_eq]

theorem material_null_coefficient_even (p : ℕ) :
    carryMaterialNullCoefficient (2*p) = canonicalCompletedNativeLogDerivativeMoment (2*p) -
      canonicalCompletedNativeLogDerivativeMoment p^2 / canonicalCompletedNativeLogDerivativeMoment 0 := by
  rw [material_null_coefficient_source,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem material_null_coefficient_odd (p : ℕ) :
    carryMaterialNullCoefficient (2*p+1) = canonicalCompletedNativeLogDerivativeMoment (2*p+1) := by
  rw [material_null_coefficient_source, show 2*p+1+1 = 2*(p+1) by omega,
    completedNativeGreenResponseTaylorCoefficient_even_eq_zero]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]

/-- Every finite order, with no sign hypothesis or target Gram. The
neighborhood may depend on the fixed order and the fixed input family. -/
theorem material_null_energy_factor (k : ℕ) (hk : 0 < k)
    {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(a i)^j) = 0) :
    ∀ᶠ e : ℝ in nhds 0,
      carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) =
        e^(2*k)*carryMaterialNullEnergy k c a e := by
  rcases material_residual_centered_kernel with ⟨U, ho, hz, hs⟩
  have hscale : carryMaterialTaylorShift 1 0 = (carryMaterialResponseScale : ℂ) := by
    change carryMaterialResponseAxis 0 = _
    rw [material_axis_zero, material_scale_eq]
  have hm : ∀ᶠ e : ℝ in nhds 0, ∀ i, e*a i ∈ U := by
    apply Filter.eventually_all.mpr
    intro i
    have ht : Tendsto (fun e : ℝ => e*a i) (nhds 0) (nhds 0) := by
      simpa only [id_eq, zero_mul] using (continuousAt_id.mul_const (a i)).tendsto (x := (0 : ℝ))
    exact ht.eventually (ho.mem_nhds hz)
  have hreg (j : Fin (k+1)) : ∀ᶠ e : ℝ in nhds 0, ∀ i,
      DifferentiableAt ℝ (carryMaterialTaylorShift (2*j.val)) (e*a i) := by
    apply Filter.eventually_all.mpr
    intro i
    have ht : Tendsto (fun e : ℝ => e*a i) (nhds 0) (nhds 0) := by
      simpa only [id_eq, zero_mul] using (continuousAt_id.mul_const (a i)).tendsto (x := (0 : ℝ))
    exact ht.eventually (material_taylor_shift_regular (2*j.val))
  have hall : ∀ᶠ e : ℝ in nhds 0, ∀ j : Fin (k+1), ∀ i,
      DifferentiableAt ℝ (carryMaterialTaylorShift (2*j.val)) (e*a i) :=
    Filter.eventually_all.mpr hreg
  filter_upwards [hm, hall] with e he hd
  exact carryMaterialNull_energy_factor hs hscale material_scale_pos k hk
    (material_taylor_shift_conj (k+1)) c a hM e he
      (fun i j _ hj => hd ⟨j, by omega⟩ i)

theorem material_null_energy_continuous (k : ℕ) {n : ℕ} (c a : Fin n → ℝ) :
    ContinuousAt (carryMaterialNullEnergy k c a) 0 :=
  carryMaterialNullEnergy_continuous k
    (material_taylor_shift_hasDerivAt_zero (k+1)).continuousAt (material_even_taylor_shift_zero k)
    (material_even_taylor_shift_hasDerivAt_zero k).differentiableAt
    (material_taylor_shift_deriv_continuous (2*k)) c a

/-- Calibration at EVERY order; no sign is assumed or concluded. -/
theorem material_null_energy_limit (k : ℕ) {n : ℕ} (c a : Fin n → ℝ) :
    Tendsto (carryMaterialNullEnergy k c a) (nhds 0)
      (nhds (carryMaterialNullCoefficient k*(∑ i, c i*(a i)^k)^2)) := by
  have h := (material_null_energy_continuous k c a).tendsto
  rw [carryMaterialNullEnergy_zero] at h
  exact h

/-- The normalized quotient is compared only on a punctured neighborhood. -/
theorem material_null_scaled_energy_limit (k : ℕ) (hk : 0 < k)
    {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(a i)^j) = 0) :
    Tendsto (fun e : ℝ => carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i)/e^(2*k))
      (nhdsWithin 0 {0}ᶜ) (nhds (carryMaterialNullCoefficient k*(∑ i, c i*(a i)^k)^2)) := by
  have heq : (fun e : ℝ => carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i)/e^(2*k))
      =ᶠ[nhdsWithin 0 {0}ᶜ] carryMaterialNullEnergy k c a := by
    filter_upwards [self_mem_nhdsWithin,
      (material_null_energy_factor k hk c a hM).filter_mono nhdsWithin_le_nhds] with e hne hf
    have he : e ≠ 0 := by simpa using hne
    rw [hf]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ he)
  exact ((material_null_energy_limit k c a).mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- Conditional sign consequence of the general identity. In the eighth
order application below the source itself discharges this coefficient sign. -/
theorem material_null_fixed_family_positive (k : ℕ) (hk : 0 < k)
    (hC : 0 < carryMaterialNullCoefficient k) {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(a i)^j) = 0)
    (hMk : (∑ i, c i*(a i)^k) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) := by
  have hpos : 0 < carryMaterialNullCoefficient k*(∑ i, c i*(a i)^k)^2 :=
    mul_pos hC (sq_pos_of_ne_zero hMk)
  have hQ := (tendsto_order.1 (material_null_energy_limit k c a)).1 0 hpos
  filter_upwards [hQ, material_null_energy_factor k hk c a hM] with e he hf hne
  rw [hf]
  have hp : 0 < e^(2*k) := by
    simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero hne) k
  exact mul_pos hp he

theorem material_null_energy_lower_bound (k : ℕ) (hk : 0 < k)
    (hC : 0 < carryMaterialNullCoefficient k) {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(a i)^j) = 0)
    (hMk : (∑ i, c i*(a i)^k) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0,
      carryMaterialNullCoefficient k*(∑ i, c i*(a i)^k)^2/2*e^(2*k) ≤
        carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) := by
  let C : ℝ := carryMaterialNullCoefficient k*(∑ i, c i*(a i)^k)^2
  have hC' : 0 < C := mul_pos hC (sq_pos_of_ne_zero hMk)
  have hlim : Tendsto (carryMaterialNullEnergy k c a) (nhds 0) (nhds C) :=
    material_null_energy_limit k c a
  have hmargin : ∀ᶠ e : ℝ in nhds 0, C/2 < carryMaterialNullEnergy k c a e :=
    (tendsto_order.1 hlim).1 (C/2) (by linarith)
  filter_upwards [hmargin, material_null_energy_factor k hk c a hM] with e he hf
  change C/2*e^(2*k) ≤ _
  rw [hf, mul_comm (C/2)]
  exact mul_le_mul_of_nonneg_left he.le (by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg e) k)

/-- A literal evaluation of the independently certified source boundary
face. The alternating middle coordinate is zero, but its source definition
and the u/w crossing are preserved; no new metric or Gram is introduced. -/
theorem material_source_five_even_specialization :
    nativeSourceFiveEvenBoundaryEnergy
      ((-(canonicalCompletedNativeLogDerivativeMoment 2 /
        canonicalCompletedNativeLogDerivativeMoment 0) : ℝ) : ℂ) 0 1 =
      2*carryMaterialNullCoefficient 4 := by
  have hC : carryMaterialNullCoefficient 4 = canonicalCompletedNativeLogDerivativeMoment 4 -
      canonicalCompletedNativeLogDerivativeMoment 2^2/canonicalCompletedNativeLogDerivativeMoment 0 := by
    simpa only [show 2*2=4 from rfl] using material_null_coefficient_even 2
  rw [hC]
  unfold nativeSourceFiveEvenBoundaryEnergy
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical]
  simp [Complex.normSq_apply]
  field_simp [canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne']
  ring

/-- The eighth-order coefficient sign is PROVED from the original theta
source certificate, not supplied by an extra positivity hypothesis. -/
theorem material_fourth_null_coefficient_pos : 0 < carryMaterialNullCoefficient 4 := by
  have h := nativeSourceFiveEvenBoundaryEnergy_pos
    ((-(canonicalCompletedNativeLogDerivativeMoment 2 /
      canonicalCompletedNativeLogDerivativeMoment 0) : ℝ) : ℂ) 0 1
    (Or.inr (Or.inr one_ne_zero))
  rw [material_source_five_even_specialization] at h
  linarith

private theorem below_four {n : ℕ} (c a : Fin n → ℝ)
    (h1 : (∑ i, c i*a i)=0) (h2 : (∑ i, c i*(a i)^2)=0) (h3 : (∑ i, c i*(a i)^3)=0) :
    ∀ j, 0 < j → j < 4 → (∑ i, c i*(a i)^j)=0 := by
  intro j hj hlt
  have he : j=1 ∨ j=2 ∨ j=3 := by omega
  rcases he with rfl | rfl | rfl
  · simpa only [pow_one] using h1
  · exact h2
  · exact h3

theorem material_fourth_null_energy_factor {n : ℕ} (c a : Fin n → ℝ)
    (h1 : (∑ i, c i*a i)=0) (h2 : (∑ i, c i*(a i)^2)=0) (h3 : (∑ i, c i*(a i)^3)=0) :
    ∀ᶠ e : ℝ in nhds 0,
      carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) =
        e^8*carryMaterialNullEnergy 4 c a e :=
  material_null_energy_factor 4 (by decide) c a (below_four c a h1 h2 h3)

theorem material_fourth_null_energy_limit {n : ℕ} (c a : Fin n → ℝ) :
    Tendsto (carryMaterialNullEnergy 4 c a) (nhds 0)
      (nhds ((canonicalCompletedNativeLogDerivativeMoment 4 -
        canonicalCompletedNativeLogDerivativeMoment 2^2/canonicalCompletedNativeLogDerivativeMoment 0)*
          (∑ i, c i*(a i)^4)^2)) := by
  have h := material_null_energy_limit 4 c a
  have hC := material_null_coefficient_even 2
  norm_num only at hC
  simpa only [hC] using h

theorem material_fourth_null_scaled_energy_limit {n : ℕ} (c a : Fin n → ℝ)
    (h1 : (∑ i, c i*a i)=0) (h2 : (∑ i, c i*(a i)^2)=0) (h3 : (∑ i, c i*(a i)^3)=0) :
    Tendsto (fun e : ℝ => carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i)/e^8)
      (nhdsWithin 0 {0}ᶜ) (nhds (carryMaterialNullCoefficient 4*(∑ i, c i*(a i)^4)^2)) :=
  material_null_scaled_energy_limit 4 (by decide) c a (below_four c a h1 h2 h3)

theorem material_fourth_null_fixed_family_positive {n : ℕ} (c a : Fin n → ℝ)
    (h1 : (∑ i, c i*a i)=0) (h2 : (∑ i, c i*(a i)^2)=0) (h3 : (∑ i, c i*(a i)^3)=0)
    (h4 : (∑ i, c i*(a i)^4) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) :=
  material_null_fixed_family_positive 4 (by decide) material_fourth_null_coefficient_pos
    c a (below_four c a h1 h2 h3) h4

theorem material_fourth_null_energy_lower_bound {n : ℕ} (c a : Fin n → ℝ)
    (h1 : (∑ i, c i*a i)=0) (h2 : (∑ i, c i*(a i)^2)=0) (h3 : (∑ i, c i*(a i)^3)=0)
    (h4 : (∑ i, c i*(a i)^4) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0,
      carryMaterialNullCoefficient 4*(∑ i, c i*(a i)^4)^2/2*e^8 ≤
        carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) :=
  material_null_energy_lower_bound 4 (by decide) material_fourth_null_coefficient_pos
    c a (below_four c a h1 h2 h3) h4

end
end CarryMaterialNullHierarchyComparison

namespace CarryMaterialNullHierarchyComparison
#assert_central_comparison_axioms material_even_taylor_shift_zero
#print axioms material_even_taylor_shift_zero
#assert_central_comparison_axioms material_even_taylor_shift_hasDerivAt_zero
#print axioms material_even_taylor_shift_hasDerivAt_zero
#assert_central_comparison_axioms material_null_coefficient_source
#print axioms material_null_coefficient_source
#assert_central_comparison_axioms material_null_coefficient_even
#print axioms material_null_coefficient_even
#assert_central_comparison_axioms material_null_coefficient_odd
#print axioms material_null_coefficient_odd
#assert_central_comparison_axioms material_null_energy_factor
#print axioms material_null_energy_factor
#assert_central_comparison_axioms material_null_energy_continuous
#print axioms material_null_energy_continuous
#assert_central_comparison_axioms material_null_energy_limit
#print axioms material_null_energy_limit
#assert_central_comparison_axioms material_null_scaled_energy_limit
#print axioms material_null_scaled_energy_limit
#assert_central_comparison_axioms material_null_fixed_family_positive
#print axioms material_null_fixed_family_positive
#assert_central_comparison_axioms material_null_energy_lower_bound
#print axioms material_null_energy_lower_bound
#assert_central_comparison_axioms material_source_five_even_specialization
#print axioms material_source_five_even_specialization
#assert_central_comparison_axioms material_fourth_null_coefficient_pos
#print axioms material_fourth_null_coefficient_pos
#assert_central_comparison_axioms material_fourth_null_energy_factor
#print axioms material_fourth_null_energy_factor
#assert_central_comparison_axioms material_fourth_null_energy_limit
#print axioms material_fourth_null_energy_limit
#assert_central_comparison_axioms material_fourth_null_scaled_energy_limit
#print axioms material_fourth_null_scaled_energy_limit
#assert_central_comparison_axioms material_fourth_null_fixed_family_positive
#print axioms material_fourth_null_fixed_family_positive
#assert_central_comparison_axioms material_fourth_null_energy_lower_bound
#print axioms material_fourth_null_energy_lower_bound
end CarryMaterialNullHierarchyComparison

namespace CarryMaterialNullHierarchyComparison
open GeometryOfNumbers.Analysis Filter CarrySelfAdjointOperator CarryMaterialThirdNullComparison
open scoped BigOperators Topology

-- Same fourth-difference family of actual source readings; M0=-1 is allowed.
example : ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
    0 < carryRealKernelEnergy carryMaterialRealResidual (![-4,6,-4,1] : Fin 4 → ℝ)
      (fun i => e*(![1,2,3,4] : Fin 4 → ℝ) i) := by
  apply material_fourth_null_fixed_family_positive ![-4,6,-4,1] ![1,2,3,4]
  all_goals norm_num [Fin.sum_univ_four,
    show (![-4,6,-4,1] : Fin 4 → ℝ) 2 = -4 from rfl,
    show (![-4,6,-4,1] : Fin 4 → ℝ) 3 = 1 from rfl,
    show (![1,2,3,4] : Fin 4 → ℝ) 2 = 3 from rfl,
    show (![1,2,3,4] : Fin 4 → ℝ) 3 = 4 from rfl]

example : Tendsto (carryMaterialNullEnergy 4 (![-4,6,-4,1] : Fin 4 → ℝ) ![1,2,3,4])
    (nhds 0) (nhds (576*carryMaterialNullCoefficient 4)) := by
  have h := material_null_energy_limit 4 (![-4,6,-4,1] : Fin 4 → ℝ) ![1,2,3,4]
  norm_num [Fin.sum_univ_four,
    show (![-4,6,-4,1] : Fin 4 → ℝ) 2 = -4 from rfl,
    show (![-4,6,-4,1] : Fin 4 → ℝ) 3 = 1 from rfl,
    show (![1,2,3,4] : Fin 4 → ℝ) 2 = 3 from rfl,
    show (![1,2,3,4] : Fin 4 → ℝ) 3 = 4 from rfl] at h
  simpa only [mul_comm] using h

-- The general energy agrees LITERALLY with PR #11, with its order-eight correction.
example {n : ℕ} (c a : Fin n → ℝ) (e : ℝ) :
    carryMaterialNullEnergy 3 c a e = carryMaterialThirdNullEnergy c a e := by
  have hS : carryMaterialNullSynthesis 3 c a e =
      (e : ℂ)*carryMaterialThirdNullSynthesis c a e := by
    unfold carryMaterialNullSynthesis carryMaterialThirdNullSynthesis
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have ht := carryMaterialTaylorShift_reconstruct 4 (e*a i)
    rw [material_fourth_taylor_shift_zero, zero_add] at ht
    rw [ht]
    push_cast
    ring
  unfold carryMaterialNullEnergy carryMaterialThirdNullEnergy
  rw [hS, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

-- Next odd coefficient is calibrated, with no all-order sign inferred.
example : carryMaterialNullCoefficient 5 = canonicalCompletedNativeLogDerivativeMoment 5 := by
  simpa only [show 2*2+1=5 from rfl] using material_null_coefficient_odd 2

-- Vanishing Mk produces a zero coefficient, not a sign theorem for the rest.
example (k : ℕ) {n : ℕ} (c a : Fin n → ℝ) (hM : (∑ i, c i*(a i)^k)=0) :
    Tendsto (carryMaterialNullEnergy k c a) (nhds 0) (nhds 0) := by
  simpa only [hM, zero_pow (by decide : 2 ≠ 0), mul_zero] using material_null_energy_limit k c a

end CarryMaterialNullHierarchyComparison

namespace CarryMaterialHierarchySignComparison
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator Filter
open CarryMaterialNullHierarchyComparison
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

local notation "h" => canonicalCompletedNativeLogDerivativeMoment
local notation "P" => nativeThetaMomentPolynomial

/-- The actual source density for the radial null coefficient. In even
order this retains BOTH ordered mixed terms and the central diagonal.
This polynomial is a ledger for a previously synthesized source, not a
new physical state, metric or positive measure. -/
def carryMaterialNullThetaPolynomial (k : ℕ) : Polynomial ℝ :=
  if k % 2 = 0 then
    P k - (2*h (k/2)/h 0) • P (k/2) + (h (k/2)/h 0)^2 • P 0
  else P k

theorem material_null_theta_even (p : ℕ) :
    carryMaterialNullThetaPolynomial (2*p) =
      P (2*p) - (2*h p/h 0) • P p + (h p/h 0)^2 • P 0 := by
  simp [carryMaterialNullThetaPolynomial]

theorem material_null_theta_odd (p : ℕ) :
    carryMaterialNullThetaPolynomial (2*p+1) = P (2*p+1) := by
  simp [carryMaterialNullThetaPolynomial]

/-- All orders, with the ORIGINAL theta kernel and its original c0
normalization. The source integral is signed; its sign is not a premise. -/
theorem material_null_theta_integral (k : ℕ) :
    nativeXiPolynomialIntegral (carryMaterialNullThetaPolynomial k) =
      carryMaterialNullCoefficient k := by
  by_cases he : k % 2 = 0
  · have hk : k = 2*(k/2) := by omega
    rw [hk, material_null_theta_even, map_add, map_sub, map_smul, map_smul]
    simp only [nativeThetaMomentPolynomial_integral, smul_eq_mul]
    rw [material_null_coefficient_even]
    field_simp [canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne']
    ring
  · have hk : k = 2*(k/2)+1 := by omega
    rw [hk, material_null_theta_odd, nativeThetaMomentPolynomial_integral,
      material_null_coefficient_odd]

theorem material_null_theta_coeff_below_two (k d : ℕ) (hd : d < 2) :
    (carryMaterialNullThetaPolynomial k).coeff d = 0 := by
  unfold carryMaterialNullThetaPolynomial
  split_ifs
  · simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_smul,
      smul_eq_mul, nativeThetaMomentPolynomial_coeff_below_two _ d hd,
      mul_zero, sub_self, add_zero]
  · exact nativeThetaMomentPolynomial_coeff_below_two k d hd

theorem material_null_theta_center_traces (k : ℕ) :
    (carryMaterialNullThetaPolynomial k).eval 0 = 0 ∧
      (carryMaterialNullThetaPolynomial k).derivative.eval 0 = 0 := by
  simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
    Nat.cast_zero, zero_add, mul_one]
  exact ⟨material_null_theta_coeff_below_two k 0 (by decide),
    material_null_theta_coeff_below_two k 1 (by decide)⟩

/-- Green transfer preserves the full source coefficient; the two central
traces vanish by a theorem, and the existing flux theorem controls infinity. -/
theorem material_null_coefficient_thetaGreen (k : ℕ) :
    carryMaterialNullCoefficient k =
      ∫ u in Set.Ioi (0 : ℝ),
        (nativeThetaGreenPolynomial (carryMaterialNullThetaPolynomial k)).eval u *
          XiThetaCosine.thetaTail u := by
  rw [← material_null_theta_integral, nativeXiPolynomialIntegral_eq_thetaGreen_integral]
  obtain ⟨h0,h1⟩ := material_null_theta_center_traces k
  simp only [h0,h1,zero_div,zero_mul,add_zero]

theorem material_null_coefficient_theta_masses (k : ℕ) :
    carryMaterialNullCoefficient k =
      nativeThetaPositiveMass (carryMaterialNullThetaPolynomial k) -
        nativeThetaNegativeMass (carryMaterialNullThetaPolynomial k) := by
  rw [← material_null_theta_integral, nativeXiPolynomialIntegral_eq_masses]

/-- Exact sign gate on this source density, not a proof of domination. -/
theorem material_null_coefficient_pos_iff_theta_dominance (k : ℕ) :
    0 < carryMaterialNullCoefficient k ↔
      nativeThetaNegativeMass (carryMaterialNullThetaPolynomial k) <
        nativeThetaPositiveMass (carryMaterialNullThetaPolynomial k) := by
  rw [material_null_coefficient_theta_masses, sub_pos]

theorem material_hierarchy_pos_iff_theta_dominance :
    (∀ k : ℕ, 0 < k → 0 < carryMaterialNullCoefficient k) ↔
      ∀ k : ℕ, 0 < k →
        nativeThetaNegativeMass (carryMaterialNullThetaPolynomial k) <
          nativeThetaPositiveMass (carryMaterialNullThetaPolynomial k) := by
  simp_rw [material_null_coefficient_pos_iff_theta_dominance]

/-- The odd original source density really has a negative highest term.
Pointwise positivity of theta alone therefore does not prove its integral's sign. -/
theorem material_null_theta_odd_top_negative (p : ℕ) :
    (carryMaterialNullThetaPolynomial (2*p+1)).coeff (2*(2*p+1)+2) < 0 := by
  rw [material_null_theta_odd, nativeThetaMomentPolynomial_coeff_top]
  apply mul_neg_of_pos_of_neg
  · exact inv_pos.mpr (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
      completedNativeRealEvenCharacteristicCoefficient_zero_ge_third)
  · unfold nativeThetaMomentTopCoefficient
    rw [pow_add, pow_mul]
    norm_num only [neg_one_sq, one_pow, pow_one, one_mul, neg_one_mul]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)

/-- The signed tail is present in the literal original theta density at
every odd hierarchy order, including orders whose total sign is certified. -/
theorem material_null_theta_odd_density_eventually_negative (p : ℕ) :
    ∀ᶠ u : ℝ in atTop,
      (carryMaterialNullThetaPolynomial (2*p+1)).eval u * completedNativeXiCosineKernel u < 0 := by
  have hd : (carryMaterialNullThetaPolynomial (2*p+1)).natDegree = 2*(2*p+1)+2 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      intro d hlt
      rw [material_null_theta_odd]
      exact nativeThetaMomentPolynomial_coeff_above _ d hlt
    · exact (material_null_theta_odd_top_negative p).ne
  have ht : Tendsto (fun u : ℝ => (carryMaterialNullThetaPolynomial (2*p+1)).eval u)
      atTop atBot := by
    apply Polynomial.tendsto_atBot_of_leadingCoeff_nonpos
    · rw [← Polynomial.natDegree_pos_iff_degree_pos, hd]
      omega
    · rw [← Polynomial.coeff_natDegree, hd]
      exact (material_null_theta_odd_top_negative p).le
  filter_upwards [ht.eventually (eventually_lt_atBot (0 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with u hu hu0
  exact mul_neg_of_neg_of_pos hu (completedNativeXiCosineKernel_pos hu0)

/-- A literal diagonal of the independently certified six-coordinate
source face. No new source or target Gram is used. -/
theorem material_source_six_odd_specialization :
    nativeSourceSixOddBoundaryEnergy 0 0 1 = 2*carryMaterialNullCoefficient 5 := by
  rw [show carryMaterialNullCoefficient 5 = h 5 by
    simpa only [show 2*2+1=5 from rfl] using material_null_coefficient_odd 2]
  unfold nativeSourceSixOddBoundaryEnergy
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical]
  simp

theorem material_fifth_null_coefficient_pos : 0 < carryMaterialNullCoefficient 5 := by
  have hp := nativeSourceSixOddBoundaryEnergy_pos 0 0 1 (Or.inr (Or.inr one_ne_zero))
  rw [material_source_six_odd_specialization] at hp
  linarith

/-- Original seven-coordinate source face on the two-coordinate direction
forced by the central channel. Its nonzero u/t crossing remains. -/
theorem material_source_seven_even_specialization :
    nativeSourceSevenEvenBoundaryEnergy (((h 3/h 0) : ℝ) : ℂ) 0 0 1 =
      2*carryMaterialNullCoefficient 6 := by
  rw [show carryMaterialNullCoefficient 6 = h 6-h 3^2/h 0 by
    simpa only [show 2*3=6 from rfl] using material_null_coefficient_even 3]
  unfold nativeSourceSevenEvenBoundaryEnergy nativeSourceFiveEvenBoundaryEnergy
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical]
  simp [Complex.normSq_apply]
  field_simp [canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne']
  ring

theorem material_sixth_null_coefficient_pos : 0 < carryMaterialNullCoefficient 6 := by
  have hp := nativeSourceSevenEvenBoundaryEnergy_pos (((h 3/h 0) : ℝ) : ℂ) 0 0 1
    (Or.inr (Or.inr (Or.inr one_ne_zero)))
  rw [material_source_seven_even_specialization] at hp
  linarith

/-- Sufficient source criterion for every fixed finite radial family. The
all-order domination premise is explicit and is NOT discharged here. -/
theorem material_null_fixed_family_positive_of_theta_dominance
    (k : ℕ) (hk : 0 < k)
    (hdom : nativeThetaNegativeMass (carryMaterialNullThetaPolynomial k) <
      nativeThetaPositiveMass (carryMaterialNullThetaPolynomial k))
    {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(a i)^j)=0)
    (hMk : (∑ i, c i*(a i)^k) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) :=
  material_null_fixed_family_positive k hk
    ((material_null_coefficient_pos_iff_theta_dominance k).mpr hdom) c a hM hMk

theorem material_fifth_null_fixed_family_positive {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < 5 → (∑ i, c i*(a i)^j)=0)
    (hMk : (∑ i, c i*(a i)^5) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) :=
  material_null_fixed_family_positive 5 (by decide) material_fifth_null_coefficient_pos c a hM hMk

theorem material_sixth_null_fixed_family_positive {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < 6 → (∑ i, c i*(a i)^j)=0)
    (hMk : (∑ i, c i*(a i)^6) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) :=
  material_null_fixed_family_positive 6 (by decide) material_sixth_null_coefficient_pos c a hM hMk

/-- Every sign through order six is discharged by the original source
certificates, independently of the radial input family. -/
theorem material_null_coefficient_pos_through_six (k : ℕ) (hk : 0 < k) (hk6 : k ≤ 6) :
    0 < carryMaterialNullCoefficient k := by
  have he : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc := material_null_coefficient_odd 0
    norm_num only at hc
    rw [hc]
    exact SourcePositiveReduction.nativeMoment_one_pos
  · have hc := material_null_coefficient_even 1
    norm_num only at hc
    rw [hc]
    have he : h 2-h 1^2/h 0 = (h 0*h 2-h 1^2)/h 0 := by
      field_simp [canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne']
    rw [he]
    exact div_pos SourcePositiveReduction.nativeMoment_first_discriminant_pos
      canonicalCompletedNativeLogDerivativeMoment_zero_pos
  · have hc := material_null_coefficient_odd 1
    norm_num only at hc
    rw [hc]
    exact CarryMaterialThirdNullComparison.material_moment_three_pos
  · exact material_fourth_null_coefficient_pos
  · exact material_fifth_null_coefficient_pos
  · exact material_sixth_null_coefficient_pos

theorem material_null_fixed_family_positive_through_six
    (k : ℕ) (hk : 0 < k) (hk6 : k ≤ 6) {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(a i)^j)=0)
    (hMk : (∑ i, c i*(a i)^k) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) :=
  material_null_fixed_family_positive k hk (material_null_coefficient_pos_through_six k hk hk6)
    c a hM hMk

local notation "ρ" => (22/175 : ℝ)

private theorem moment_abs_bound (k : ℕ) : |h k| ≤ ρ^(k+1) := by
  have hb := canonicalCompletedNativeLogDerivativeMoment_sharp_decay k
  have hn : 0 ≤ (1/25 : ℝ)^(k+1) := by positivity
  linarith

/-- An unconditional bound at EVERY order of the actual source hierarchy.
It is an upper bound on magnitude and does not supply a positive sign. -/
theorem material_null_coefficient_decay_bound (k : ℕ) :
    |carryMaterialNullCoefficient k| ≤ (1+ρ/h 0)*ρ^(k+1) := by
  by_cases he : k % 2 = 0
  · have hk : k = 2*(k/2) := by omega
    rw [hk, material_null_coefficient_even]
    have hs : (h (k/2))^2 ≤ (ρ^(k/2+1))^2 := by
      nlinarith [moment_abs_bound (k/2), abs_nonneg (h (k/2)),
        sq_abs (h (k/2)), pow_nonneg (by norm_num : (0:ℝ) ≤ ρ) (k/2+1)]
    calc
      |h (2*(k/2)) - h (k/2)^2/h 0| ≤
          |h (2*(k/2))| + |h (k/2)^2/h 0| := abs_sub _ _
      _ ≤ ρ^(2*(k/2)+1) + (ρ^(k/2+1))^2/h 0 := by
        apply add_le_add (moment_abs_bound _)
        rw [abs_div, abs_of_nonneg (sq_nonneg _),
          abs_of_pos canonicalCompletedNativeLogDerivativeMoment_zero_pos]
        exact div_le_div_of_nonneg_right hs canonicalCompletedNativeLogDerivativeMoment_zero_pos.le
      _ = (1+ρ/h 0)*ρ^(2*(k/2)+1) := by
        rw [← pow_mul, show (k/2+1)*2=(2*(k/2)+1)+1 by omega, pow_succ]
        ring
  · have hk : k = 2*(k/2)+1 := by omega
    rw [hk, material_null_coefficient_odd]
    calc
      |h (2*(k/2)+1)| ≤ ρ^(2*(k/2)+1+1) := moment_abs_bound _
      _ ≤ (1+ρ/h 0)*ρ^(2*(k/2)+1+1) := by
        have hz : 0 ≤ (ρ/h 0)*ρ^(2*(k/2)+1+1) := by
          positivity [canonicalCompletedNativeLogDerivativeMoment_zero_pos]
        linarith

theorem material_null_coefficients_tendsto_zero :
    Tendsto carryMaterialNullCoefficient atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero (fun _ => abs_nonneg _) material_null_coefficient_decay_bound
  have hp : Tendsto (fun k : ℕ => ρ^k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [pow_succ, zero_mul, mul_zero] using
    (hp.mul_const ρ).const_mul (1+ρ/h 0)

/-- Even if every individual sign is positive, there can be no fixed
positive lower bound across orders in the unchanged source normalization. -/
theorem material_no_uniform_positive_coefficient_floor :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ, 0 < k → δ ≤ carryMaterialNullCoefficient k := by
  rintro ⟨δ,hδ,hfloor⟩
  have hsmall := (tendsto_order.mp material_null_coefficients_tendsto_zero).2 δ hδ
  obtain ⟨k,hk,hk1⟩ := (hsmall.and (eventually_ge_atTop (1:ℕ))).exists
  exact (not_lt_of_ge (hfloor k (by omega))) hk

end
end CarryMaterialHierarchySignComparison

namespace CarryMaterialHierarchySignComparison
#assert_central_comparison_axioms carryMaterialNullThetaPolynomial
#print axioms carryMaterialNullThetaPolynomial
#assert_central_comparison_axioms material_null_theta_even
#print axioms material_null_theta_even
#assert_central_comparison_axioms material_null_theta_odd
#print axioms material_null_theta_odd
#assert_central_comparison_axioms material_null_theta_integral
#print axioms material_null_theta_integral
#assert_central_comparison_axioms material_null_theta_coeff_below_two
#print axioms material_null_theta_coeff_below_two
#assert_central_comparison_axioms material_null_theta_center_traces
#print axioms material_null_theta_center_traces
#assert_central_comparison_axioms material_null_coefficient_thetaGreen
#print axioms material_null_coefficient_thetaGreen
#assert_central_comparison_axioms material_null_coefficient_theta_masses
#print axioms material_null_coefficient_theta_masses
#assert_central_comparison_axioms material_null_coefficient_pos_iff_theta_dominance
#print axioms material_null_coefficient_pos_iff_theta_dominance
#assert_central_comparison_axioms material_hierarchy_pos_iff_theta_dominance
#print axioms material_hierarchy_pos_iff_theta_dominance
#assert_central_comparison_axioms material_null_theta_odd_top_negative
#print axioms material_null_theta_odd_top_negative
#assert_central_comparison_axioms material_null_theta_odd_density_eventually_negative
#print axioms material_null_theta_odd_density_eventually_negative
#assert_central_comparison_axioms material_source_six_odd_specialization
#print axioms material_source_six_odd_specialization
#assert_central_comparison_axioms material_fifth_null_coefficient_pos
#print axioms material_fifth_null_coefficient_pos
#assert_central_comparison_axioms material_source_seven_even_specialization
#print axioms material_source_seven_even_specialization
#assert_central_comparison_axioms material_sixth_null_coefficient_pos
#print axioms material_sixth_null_coefficient_pos
#assert_central_comparison_axioms material_null_fixed_family_positive_of_theta_dominance
#print axioms material_null_fixed_family_positive_of_theta_dominance
#assert_central_comparison_axioms material_fifth_null_fixed_family_positive
#print axioms material_fifth_null_fixed_family_positive
#assert_central_comparison_axioms material_sixth_null_fixed_family_positive
#print axioms material_sixth_null_fixed_family_positive
#assert_central_comparison_axioms material_null_coefficient_pos_through_six
#print axioms material_null_coefficient_pos_through_six
#assert_central_comparison_axioms material_null_fixed_family_positive_through_six
#print axioms material_null_fixed_family_positive_through_six
#assert_central_comparison_axioms material_null_coefficient_decay_bound
#print axioms material_null_coefficient_decay_bound
#assert_central_comparison_axioms material_null_coefficients_tendsto_zero
#print axioms material_null_coefficients_tendsto_zero
#assert_central_comparison_axioms material_no_uniform_positive_coefficient_floor
#print axioms material_no_uniform_positive_coefficient_floor
end CarryMaterialHierarchySignComparison

namespace CarryMaterialHierarchySignComparison
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator Filter
open CarryMaterialNullHierarchyComparison
open scoped BigOperators Topology

-- Higher finite differences of actual source readings, allowing M0 ≠ 0.
example : ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
    0 < carryRealKernelEnergy carryMaterialRealResidual (![5,-10,10,-5,1] : Fin 5 → ℝ)
      (fun i => e*(![1,2,3,4,5] : Fin 5 → ℝ) i) := by
  apply material_fifth_null_fixed_family_positive ![5,-10,10,-5,1] ![1,2,3,4,5]
  · intro j hj hlt
    interval_cases j <;> norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]

example : ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
    0 < carryRealKernelEnergy carryMaterialRealResidual (![-6,15,-20,15,-6,1] : Fin 6 → ℝ)
      (fun i => e*(![1,2,3,4,5,6] : Fin 6 → ℝ) i) := by
  apply material_sixth_null_fixed_family_positive ![-6,15,-20,15,-6,1] ![1,2,3,4,5,6]
  · intro j hj hlt
    interval_cases j <;> norm_num [Fin.sum_univ_succ]
  · norm_num [Fin.sum_univ_succ]

example : Tendsto
    (carryMaterialNullEnergy 5 (![5,-10,10,-5,1] : Fin 5 → ℝ) ![1,2,3,4,5])
    (nhds 0) (nhds (14400*carryMaterialNullCoefficient 5)) := by
  have h := material_null_energy_limit 5 (![5,-10,10,-5,1] : Fin 5 → ℝ) ![1,2,3,4,5]
  norm_num [Fin.sum_univ_succ] at h
  simpa only [mul_comm] using h

example : Tendsto
    (carryMaterialNullEnergy 6 (![-6,15,-20,15,-6,1] : Fin 6 → ℝ) ![1,2,3,4,5,6])
    (nhds 0) (nhds (518400*carryMaterialNullCoefficient 6)) := by
  have h := material_null_energy_limit 6 (![-6,15,-20,15,-6,1] : Fin 6 → ℝ) ![1,2,3,4,5,6]
  norm_num [Fin.sum_univ_succ] at h
  simpa only [mul_comm] using h

-- Next order is identified, with NO unsupported sign claim.
example : carryMaterialNullCoefficient 7 = canonicalCompletedNativeLogDerivativeMoment 7 := by
  simpa only [show 2*3+1=7 from rfl] using material_null_coefficient_odd 3

-- The all-order bound is unconditional, and uses the unchanged normalization.
example : Tendsto carryMaterialNullCoefficient atTop (nhds 0) :=
  material_null_coefficients_tendsto_zero

end CarryMaterialHierarchySignComparison

namespace CarryMaterialPoleDominanceComparison
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator Filter
open CarryMaterialNullHierarchyComparison CarryMaterialHierarchySignComparison
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

local notation "h" => canonicalCompletedNativeLogDerivativeMoment
local notation "μ" => completedNativeXiCosineMoment

/-- A ruler from the EXISTING source integrals, with no pole premise. -/
theorem material_moment_zero_ge_one_fiftieth : (1/50 : ℝ) ≤ h 0 := by
  have h0 : 0 < μ 0 := completedNativeXiCosineMoment_pos 0
  have hm := completedNativeXiCosineMoment_one_ge_287_div_12500
  have hu := completedNativeXiCosineMoment_zero_lt_249_div_500
  rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_secondOrderRatio,
    completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder 0,
    completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder 1]
  norm_num only [pow_zero,pow_one,zero_mul,one_mul,div_one,Nat.factorial] at ⊢
  apply (le_div_iff₀ h0).mpr
  nlinarith

private theorem material_moment_one_cosine_formula :
    h 1 = μ 1^2/(4*μ 0^2)-μ 2/(12*μ 0) := by
  rw [canonicalCompletedNativeLogDerivativeMoment_one_eq_fourthOrderDiscriminant]
  simp only [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
  norm_num only [Nat.factorial, Nat.reduceMul, pow_zero, pow_one, neg_one_sq,
    one_mul, div_one]
  field_simp [(completedNativeXiCosineMoment_pos 0).ne']
  ring

/-- The second input to the tail budget is also certified by the original
theta source. No new quadrature and no positive moment model is supplied. -/
theorem material_moment_one_le_nineteen_five_hundred_thousand :
    h 1 ≤ (19/500000 : ℝ) := by
  obtain ⟨ht0l,ht0u⟩ := completedNativeThetaTailMoment_zero_certified_bounds
  obtain ⟨ht2l,ht2u⟩ := completedNativeThetaTailMoment_two_certified_bounds
  obtain ⟨ht4l,ht4u⟩ := completedNativeThetaTailMoment_four_certified_bounds
  have he0 := completedNativeXiCosineMoment_zero_eq_thetaTailMoments
  have he1 := completedNativeXiCosineMoment_one_eq_thetaTailMoments
  have he2 := completedNativeXiCosineMoment_two_eq_thetaTailMoments
  have hc0l : (1988479/4000000 : ℝ) ≤ μ 0 := by linarith
  have hc0u : μ 0 ≤ (19884847/40000000 : ℝ) := by linarith
  have hc1u : μ 1 ≤ (4596037/200000000 : ℝ) := by linarith
  have hc2l : (11848451/4000000000 : ℝ) ≤ μ 2 := by linarith
  have hs : μ 1^2 ≤ (4596037/200000000 : ℝ)^2 :=
    (sq_le_sq₀ (completedNativeXiCosineMoment_pos 1).le (by norm_num)).mpr hc1u
  have hd : (4 : ℝ)*(1988479/4000000)^2 ≤ 4*μ 0^2 := by
    nlinarith [(sq_le_sq₀ (by norm_num : (0:ℝ) ≤ 1988479/4000000) (completedNativeXiCosineMoment_pos 0).le).mpr hc0l]
  have ha : μ 1^2/(4*μ 0^2) ≤
      (4596037/200000000 : ℝ)^2/(4*(1988479/4000000)^2) := by
    calc
      _ ≤ (4596037/200000000 : ℝ)^2/(4*μ 0^2) :=
        div_le_div_of_nonneg_right hs (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
  have hb : (11848451/4000000000 : ℝ)/(12*(19884847/40000000)) ≤ μ 2/(12*μ 0) := by
    calc
      _ ≤ (11848451/4000000000 : ℝ)/(12*μ 0) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity [completedNativeXiCosineMoment_pos 0])
          (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right hc2l (by positivity [completedNativeXiCosineMoment_pos 0])
  rw [material_moment_one_cosine_formula]
  linarith

/-- A literal subtraction from the already synthesized source moments.
The parameter a has NOT been identified with a pole by this definition. -/
def carryMaterialPoleRemainder (a : ℝ) (n : ℕ) : ℝ := h n-a^(n+1)

/-- The existing finite-factor ledger identifies the remainder with an
actual analytic quotient jet of the ORIGINAL native characteristic.
The variable u here is the existing height-squared germ, not material time. -/
theorem material_pole_remainder_eq_quotient_jet (a : ℝ) (n : ℕ) :
    (carryMaterialPoleRemainder a n : ℂ) =
      -iteratedDeriv n (logDeriv (fun u : ℂ =>
        completedNativeEvenCharacteristic u/(1-(a : ℂ)*u))) 0/(n.factorial : ℂ) := by
  have he := AllOrderLogJet.nativeMoment_eq_finiteFactors_add_remainder
    ({0} : Finset ℕ) (fun _ => (a : ℂ)) n
  simp only [Finset.sum_singleton,Finset.prod_singleton] at he
  unfold carryMaterialPoleRemainder
  push_cast
  linear_combination he

/-- Existing valve uniqueness identifies the elementary factor. This is a
formal-series calculation, not evidence of an analytic source pole. -/
theorem material_elementary_factor_valve (a : ℝ) :
    (1-PowerSeries.C a*PowerSeries.X : PowerSeries ℝ) =
      CarrySelfAdjointOperator.ProjectiveValve.projectiveValveMass (-(PowerSeries.mk (fun n => a^(n+1)))) := by
  let G : PowerSeries ℝ := PowerSeries.mk (fun n => a^(n+1))
  have hg : G*(1-PowerSeries.C a*PowerSeries.X) = PowerSeries.C a := by
    rw [mul_sub,mul_one]
    have he : G*(PowerSeries.C a*PowerSeries.X) = PowerSeries.X*(PowerSeries.C a*G) := by ring
    rw [he]
    ext n
    cases n with
    | zero => simp [G]
    | succ n => simp [G,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_C_mul,pow_succ]; ring
  apply CarrySelfAdjointOperator.ProjectiveValve.projectiveValveMass_unique
  · simp
  · change (PowerSeries.derivative ℝ) (1-PowerSeries.C a*PowerSeries.X) = -G*(1-PowerSeries.C a*PowerSeries.X)
    rw [neg_mul,hg]
    simp [Derivation.leibniz,smul_eq_mul]

/-- A literal source/valve deflation identity for EVERY a. No root, disk
of continuation or convergence beyond the initial germ follows from it. -/
theorem material_source_formal_deflation (a : ℝ) :
    normalizedCompletedNativeEvenFormalSeries =
      (1-PowerSeries.C a*PowerSeries.X : PowerSeries ℝ)*
        CarrySelfAdjointOperator.ProjectiveValve.projectiveValveMass (-(PowerSeries.mk (carryMaterialPoleRemainder a))) := by
  rw [normalizedCompletedNativeEvenFormalSeries_eq_valveMass_neg,
    material_elementary_factor_valve,← CarrySelfAdjointOperator.ProjectiveValve.projectiveValveMass_add]
  congr 1
  ext n
  simp [carryMaterialPoleRemainder]
  ring

/-- The two ordered principal/remainder crosses and the remainder square
are retained exactly, before any lower estimate. -/
theorem material_even_null_pole_ledger (a : ℝ) (p : ℕ) :
    carryMaterialNullCoefficient (2*p) =
      a^(2*p+1)*(1-a/h 0) + carryMaterialPoleRemainder a (2*p) -
        2*a^(p+1)*carryMaterialPoleRemainder a p/h 0 -
        (carryMaterialPoleRemainder a p)^2/h 0 := by
  rw [material_null_coefficient_even]
  unfold carryMaterialPoleRemainder
  have he : (a^(p+1))^2 = a^(2*p+1)*a := by
    rw [← pow_mul, show (p+1)*2=(2*p+1)+1 by omega, pow_succ]
  field_simp [canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne']
  nlinarith [he]

private theorem pole_parameter_pos {a : ℝ} (ha : (25/5041 : ℝ) ≤ a) : 0 < a := by
  linarith

theorem material_pole_parameter_budget {a : ℝ}
    (ha : (25/5041 : ℝ) ≤ a) (hau : a ≤ (1/196 : ℝ)) :
    a ≤ (13/50 : ℝ)*h 0 ∧ (1/400 : ℝ) ≤ (51/100 : ℝ)*a := by
  constructor
  · linarith [material_moment_zero_ge_one_fiftieth]
  · linarith

/-- A concrete square-mass budget. The upper moment bound and a's range
are source-facing data; the inequality is not the desired null sign. -/
theorem material_pole_square_budget {a S : ℝ} (ha : (25/5041 : ℝ) ≤ a)
    (hS : (99/100 : ℝ)*S ≤ h 1-a^2) : S ≤ (3/5 : ℝ)*a^2 := by
  have hs : (25/5041 : ℝ)^2 ≤ a^2 :=
    (sq_le_sq₀ (by norm_num) (pole_parameter_pos ha).le).mpr ha
  nlinarith [material_moment_one_le_nineteen_five_hundred_thousand]

/-- Elementary geometry of a candidate remaining source pole. This does
not assert that such poles enumerate the source. Small imaginary offsets
are retained, rather than replaced by real positive atoms. -/
theorem material_reciprocal_squared_strip_budget (τ : ℂ)
    (hx : (20 : ℝ) ≤ τ.re) (hy : |τ.im| ≤ (1/2 : ℝ)) :
    ‖(τ^2)⁻¹‖ ≤ (1/400 : ℝ) ∧
      (99/100 : ℝ)*‖(τ^2)⁻¹‖^2 ≤ (((τ^2)⁻¹)^2).re := by
  have hτ : τ ≠ 0 := by intro hz; simp only [hz,Complex.zero_re] at hx; linarith
  have hz : τ^2 ≠ 0 := pow_ne_zero _ hτ
  have hD : 0 < Complex.normSq (τ^2) := Complex.normSq_pos.mpr hz
  have hx2 : (400 : ℝ) ≤ τ.re^2 := by nlinarith
  have hy2 : τ.im^2 ≤ (1/4 : ℝ) := by nlinarith [sq_abs τ.im,abs_nonneg τ.im]
  constructor
  · rw [norm_inv,norm_pow]
    have hb : (400 : ℝ) ≤ ‖τ‖^2 := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      nlinarith [sq_nonneg τ.im]
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 400) hb)
  · have hgeom : (99/100 : ℝ)*Complex.normSq (τ^2) ≤ (τ^2).re^2-(τ^2).im^2 := by
      simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
      nlinarith [mul_nonneg (sq_nonneg τ.re)
        (show 0 ≤ τ.re^2-798*τ.im^2 by nlinarith)]
    have ht := div_le_div_of_nonneg_right hgeom (sq_nonneg (Complex.normSq (τ^2)))
    have hre (z : ℂ) : (z^2).re=z.re*z.re-z.im*z.im := by simp only [pow_two,Complex.mul_re]
    rw [hre]
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_inv,Complex.inv_re,Complex.inv_im]
    convert ht using 1 <;> first | rfl | field_simp [hD.ne']

/-- A quantitative all-order implication on the actual source. Its tail
premise is explicit; the source has not yet been proved to satisfy it. -/
theorem material_null_coefficient_lower_of_pole_tail {a : ℝ}
    (ha : (25/5041 : ℝ) ≤ a) (hau : a ≤ (1/196 : ℝ))
    (htail : ∀ n : ℕ, 0 < n → |carryMaterialPoleRemainder a n| ≤
      (3/5 : ℝ)*a^(n+1)*(51/100 : ℝ)^(n-1))
    (k : ℕ) (hk : 0 < k) :
    (71/2500 : ℝ)*a^(k+1) ≤ carryMaterialNullCoefficient k := by
  have hap : 0 < a := pole_parameter_pos ha
  have hb := (material_pole_parameter_budget ha hau).1
  have hrough (n : ℕ) (hn : 0 < n) :
      |carryMaterialPoleRemainder a n| ≤ (3/5 : ℝ)*a^(n+1) := by
    have hp : (51/100 : ℝ)^(n-1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact (htail n hn).trans (by nlinarith [pow_nonneg hap.le (n+1)])
  have hm (n : ℕ) (hn : 0 < n) : |h n| ≤ (8/5 : ℝ)*a^(n+1) := by
    calc
      |h n| = |carryMaterialPoleRemainder a n+a^(n+1)| := by
        unfold carryMaterialPoleRemainder
        ring_nf
      _ ≤ |carryMaterialPoleRemainder a n|+|a^(n+1)| := abs_add_le _ _
      _ ≤ _ := by rw [abs_of_pos (pow_pos hap _)]; linarith [hrough n hn]
  by_cases he : k%2=0
  · have hek : k=2*(k/2) := by omega
    let p := k/2
    have hp : 0 < p := by dsimp [p]; omega
    have htheta : (51/100 : ℝ)^(2*p-1) ≤ (51/100 : ℝ) := by
      rw [show 2*p-1=(2*p-2)+1 by omega, pow_succ]
      nlinarith [pow_le_one₀ (by norm_num : (0:ℝ) ≤ 51/100)
        (by norm_num : (51/100:ℝ) ≤ 1) (n := 2*p-2)]
    have hlow : (1-(3/5 : ℝ)*(51/100))*a^(2*p+1) ≤ h (2*p) := by
      have ht := (abs_le.mp (htail (2*p) (by omega))).1
      dsimp [carryMaterialPoleRemainder] at ht
      nlinarith [mul_le_mul_of_nonneg_left htheta
        (show 0 ≤ (3/5:ℝ)*a^(2*p+1) by positivity)]
    have hs : (h p)^2 ≤ (8/5 : ℝ)^2*(a^(p+1))^2 := by
      nlinarith [hm p hp, abs_nonneg (h p), sq_abs (h p), pow_pos hap (p+1)]
    have heq : (a^(p+1))^2=a^(2*p+1)*a := by
      rw [← pow_mul,show (p+1)*2=(2*p+1)+1 by omega,pow_succ]
    rw [heq] at hs
    have hc : (h p)^2/h 0 ≤ (13/50 : ℝ)*(8/5 : ℝ)^2*a^(2*p+1) := by
      apply (div_le_iff₀ canonicalCompletedNativeLogDerivativeMoment_zero_pos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hb
        (show 0 ≤ (8/5 : ℝ)^2*a^(2*p+1) by positivity)]
    rw [hek,material_null_coefficient_even]
    change (71/2500 : ℝ)*a^(2*p+1) ≤ h (2*p)-(h p)^2/h 0
    linarith
  · have hek : k=2*(k/2)+1 := by omega
    have hl := (abs_le.mp (hrough k hk)).1
    dsimp [carryMaterialPoleRemainder] at hl
    rw [hek,material_null_coefficient_odd]
    rw [← hek]
    nlinarith [pow_pos hap (k+1)]

theorem material_theta_dominance_all_of_pole_tail {a : ℝ}
    (ha : (25/5041 : ℝ) ≤ a) (hau : a ≤ (1/196 : ℝ))
    (htail : ∀ n : ℕ, 0 < n → |carryMaterialPoleRemainder a n| ≤
      (3/5 : ℝ)*a^(n+1)*(51/100 : ℝ)^(n-1)) :
    ∀ k : ℕ, 0 < k →
      nativeThetaNegativeMass (carryMaterialNullThetaPolynomial k) <
        nativeThetaPositiveMass (carryMaterialNullThetaPolynomial k) := by
  intro k hk
  apply (material_null_coefficient_pos_iff_theta_dominance k).mp
  exact lt_of_lt_of_le (by positivity [pole_parameter_pos ha])
    (material_null_coefficient_lower_of_pole_tail ha hau htail k hk)

/-- A sufficient estimate on a concrete function of the source itself.
There is no freely chosen readout or desired Gram in this hypothesis.
The uniform quotient-jet estimate is still an unproved source obligation. -/
theorem material_theta_dominance_all_of_quotient_jet_bound {a : ℝ}
    (ha : (25/5041 : ℝ) ≤ a) (hau : a ≤ (1/196 : ℝ))
    (hjet : ∀ n : ℕ, 0 < n →
      ‖-iteratedDeriv n (logDeriv (fun u : ℂ =>
        completedNativeEvenCharacteristic u/(1-(a : ℂ)*u))) 0/(n.factorial : ℂ)‖ ≤
        (3/5 : ℝ)*a^(n+1)*(51/100 : ℝ)^(n-1)) :
    ∀ k : ℕ, 0 < k → nativeThetaNegativeMass (carryMaterialNullThetaPolynomial k) <
      nativeThetaPositiveMass (carryMaterialNullThetaPolynomial k) := by
  apply material_theta_dominance_all_of_pole_tail ha hau
  intro n hn
  have hb := hjet n hn
  rw [← material_pole_remainder_eq_quotient_jet] at hb
  simpa only [Complex.norm_real,Real.norm_eq_abs] using hb

private theorem reciprocal_power_bound (v : ℕ → ℂ)
    (hv : ∀ j, ‖v j‖ ≤ (1/400 : ℝ)) (n : ℕ) (hn : 0 < n) (j : ℕ) :
    |((v j)^(n+1)).re| ≤ ‖v j‖^2*(1/400 : ℝ)^(n-1) := by
  calc
    _ ≤ ‖(v j)^(n+1)‖ := Complex.abs_re_le_norm _
    _ = ‖v j‖^2*‖v j‖^(n-1) := by
      rw [norm_pow, ← pow_add, show 2+(n-1)=n+1 by omega]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hv j) _) (sq_nonneg _)

private theorem reciprocal_power_summable (v : ℕ → ℂ)
    (hs : Summable (fun j => ‖v j‖^2)) (hv : ∀ j, ‖v j‖ ≤ (1/400 : ℝ))
    (n : ℕ) (hn : 0 < n) : Summable (fun j => ((v j)^(n+1)).re) := by
  apply Summable.of_norm_bounded (hs.mul_right ((1/400 : ℝ)^(n-1)))
  intro j
  simpa only [Real.norm_eq_abs] using reciprocal_power_bound v hv n hn j

/-- This is a contract on coefficients of the ACTUAL source h, not on a
freely chosen moment sequence. The v_j are candidate reciprocal squared
source poles; their source readout and sector bounds are NOT constructed here.
They need not be real or have positive higher powers. -/
theorem material_pole_tail_of_complex_readout {a : ℝ} (ha : (25/5041 : ℝ) ≤ a)
    (v : ℕ → ℂ) (hs : Summable (fun j => ‖v j‖^2))
    (hv : ∀ j, ‖v j‖ ≤ (1/400 : ℝ))
    (hsector : ∀ j, (99/100 : ℝ)*‖v j‖^2 ≤ ((v j)^2).re)
    (hread : ∀ n : ℕ, 0 < n → h n = a^(n+1)+∑' j, ((v j)^(n+1)).re) :
    ∀ n : ℕ, 0 < n → |carryMaterialPoleRemainder a n| ≤
      (3/5 : ℝ)*a^(n+1)*(51/100 : ℝ)^(n-1) := by
  have hap := pole_parameter_pos ha
  have hr1 : h 1 = a^2+∑' j, ((v j)^2).re := hread 1 (by decide)
  have hsumre : Summable (fun j => ((v j)^2).re) :=
    reciprocal_power_summable v hs hv 1 (by decide)
  have hbudget : (∑' j, ‖v j‖^2) ≤ (3/5 : ℝ)*a^2 := by
    apply material_pole_square_budget ha
    have ht := Summable.tsum_le_tsum hsector (hs.mul_left (99/100 : ℝ)) hsumre
    rw [tsum_mul_left] at ht
    linarith
  intro n hn
  have hsn := reciprocal_power_summable v hs hv n hn
  have hpoint := reciprocal_power_bound v hv n hn
  have hq : (1/400 : ℝ)^(n-1) ≤ ((51/100 : ℝ)*a)^(n-1) :=
    pow_le_pow_left₀ (by norm_num) (by linarith) _
  calc
    |carryMaterialPoleRemainder a n| = |∑' j, ((v j)^(n+1)).re| := by
      simp only [carryMaterialPoleRemainder,hread n hn,add_sub_cancel_left]
    _ ≤ ∑' j, |((v j)^(n+1)).re| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsn.norm
    _ ≤ ∑' j, ‖v j‖^2*(1/400 : ℝ)^(n-1) :=
      Summable.tsum_le_tsum hpoint (by simpa only [Real.norm_eq_abs] using hsn.norm)
        (hs.mul_right _)
    _ = (∑' j, ‖v j‖^2)*(1/400 : ℝ)^(n-1) := tsum_mul_right
    _ ≤ (3/5 : ℝ)*a^2*(1/400 : ℝ)^(n-1) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ ≤ (3/5 : ℝ)*a^2*((51/100 : ℝ)*a)^(n-1) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (3/5 : ℝ)*a^(n+1)*(51/100 : ℝ)^(n-1) := by
      rw [mul_pow]
      have he : a^2*a^(n-1)=a^(n+1) := by
        rw [← pow_add,show 2+(n-1)=n+1 by omega]
      calc
        _ = (3/5 : ℝ)*(a^2*a^(n-1))*(51/100 : ℝ)^(n-1) := by ring
        _ = _ := by rw [he]

/-- ALL-order source signs follow from one first-pole range, a square-
summable separated tail, its second-power sector bound, and the exact
source readout. No higher tail sign or Hankel positivity is assumed.
Existence and source identification of that pole readout remain open here. -/
theorem material_hierarchy_positive_of_complex_pole_readout {a : ℝ}
    (ha : (25/5041 : ℝ) ≤ a) (hau : a ≤ (1/196 : ℝ))
    (v : ℕ → ℂ) (hs : Summable (fun j => ‖v j‖^2))
    (hv : ∀ j, ‖v j‖ ≤ (1/400 : ℝ))
    (hsector : ∀ j, (99/100 : ℝ)*‖v j‖^2 ≤ ((v j)^2).re)
    (hread : ∀ n : ℕ, 0 < n → h n = a^(n+1)+∑' j, ((v j)^(n+1)).re) :
    ∀ k : ℕ, 0 < k → (71/2500 : ℝ)*a^(k+1) ≤ carryMaterialNullCoefficient k := by
  exact material_null_coefficient_lower_of_pole_tail ha hau
    (material_pole_tail_of_complex_readout ha v hs hv hsector hread)

theorem material_theta_dominance_all_of_complex_pole_readout {a : ℝ}
    (ha : (25/5041 : ℝ) ≤ a) (hau : a ≤ (1/196 : ℝ))
    (v : ℕ → ℂ) (hs : Summable (fun j => ‖v j‖^2))
    (hv : ∀ j, ‖v j‖ ≤ (1/400 : ℝ))
    (hsector : ∀ j, (99/100 : ℝ)*‖v j‖^2 ≤ ((v j)^2).re)
    (hread : ∀ n : ℕ, 0 < n → h n = a^(n+1)+∑' j, ((v j)^(n+1)).re) :
    ∀ k : ℕ, 0 < k → nativeThetaNegativeMass (carryMaterialNullThetaPolynomial k) <
      nativeThetaPositiveMass (carryMaterialNullThetaPolynomial k) :=
  material_theta_dominance_all_of_pole_tail ha hau
    (material_pole_tail_of_complex_readout ha v hs hv hsector hread)

theorem material_first_pole_interval_budget (t : ℝ)
    (ht : (14 : ℝ) ≤ t) (htu : t ≤ (71/5 : ℝ)) :
    (25/5041 : ℝ) ≤ 1/t^2 ∧ 1/t^2 ≤ (1/196 : ℝ) := by
  have htl : (196 : ℝ) ≤ t^2 := by nlinarith
  have hth : t^2 ≤ (5041/25 : ℝ) := by nlinarith
  constructor
  · calc
      (25/5041 : ℝ) = 1/(5041/25 : ℝ) := by norm_num
      _ ≤ _ := one_div_le_one_div_of_le (by nlinarith) hth
  · exact one_div_le_one_div_of_le (by norm_num) htl

/-- A concrete all-order criterion using locations of candidate complex
source poles. The only identification premise is the literal source
readout. No source pole enumeration or readout is supplied by this theorem. -/
theorem material_theta_dominance_all_of_separated_readout (t : ℝ)
    (ht : (14 : ℝ) ≤ t) (htu : t ≤ (71/5 : ℝ)) (τ : ℕ → ℂ)
    (hs : Summable (fun j => ‖((τ j)^2)⁻¹‖^2))
    (hx : ∀ j, (20 : ℝ) ≤ (τ j).re) (hy : ∀ j, |(τ j).im| ≤ (1/2 : ℝ))
    (hread : ∀ n : ℕ, 0 < n →
      h n = (1/t^2)^(n+1)+∑' j, ((((τ j)^2)⁻¹)^(n+1)).re) :
    ∀ k : ℕ, 0 < k → nativeThetaNegativeMass (carryMaterialNullThetaPolynomial k) <
      nativeThetaPositiveMass (carryMaterialNullThetaPolynomial k) := by
  obtain ⟨ha,hau⟩ := material_first_pole_interval_budget t ht htu
  apply material_theta_dominance_all_of_complex_pole_readout ha hau
    (fun j => ((τ j)^2)⁻¹) hs
  · exact fun j => (material_reciprocal_squared_strip_budget (τ j) (hx j) (hy j)).1
  · exact fun j => (material_reciprocal_squared_strip_budget (τ j) (hx j) (hy j)).2
  · exact hread

end
end CarryMaterialPoleDominanceComparison

namespace CarryMaterialPoleDominanceComparison
#assert_central_comparison_axioms material_moment_zero_ge_one_fiftieth
#print axioms material_moment_zero_ge_one_fiftieth
#assert_central_comparison_axioms material_moment_one_le_nineteen_five_hundred_thousand
#print axioms material_moment_one_le_nineteen_five_hundred_thousand
#assert_central_comparison_axioms carryMaterialPoleRemainder
#print axioms carryMaterialPoleRemainder
#assert_central_comparison_axioms material_pole_remainder_eq_quotient_jet
#print axioms material_pole_remainder_eq_quotient_jet
#assert_central_comparison_axioms material_elementary_factor_valve
#print axioms material_elementary_factor_valve
#assert_central_comparison_axioms material_source_formal_deflation
#print axioms material_source_formal_deflation
#assert_central_comparison_axioms material_even_null_pole_ledger
#print axioms material_even_null_pole_ledger
#assert_central_comparison_axioms material_pole_parameter_budget
#print axioms material_pole_parameter_budget
#assert_central_comparison_axioms material_pole_square_budget
#print axioms material_pole_square_budget
#assert_central_comparison_axioms material_reciprocal_squared_strip_budget
#print axioms material_reciprocal_squared_strip_budget
#assert_central_comparison_axioms material_null_coefficient_lower_of_pole_tail
#print axioms material_null_coefficient_lower_of_pole_tail
#assert_central_comparison_axioms material_theta_dominance_all_of_pole_tail
#print axioms material_theta_dominance_all_of_pole_tail
#assert_central_comparison_axioms material_theta_dominance_all_of_quotient_jet_bound
#print axioms material_theta_dominance_all_of_quotient_jet_bound
#assert_central_comparison_axioms material_pole_tail_of_complex_readout
#print axioms material_pole_tail_of_complex_readout
#assert_central_comparison_axioms material_hierarchy_positive_of_complex_pole_readout
#print axioms material_hierarchy_positive_of_complex_pole_readout
#assert_central_comparison_axioms material_theta_dominance_all_of_complex_pole_readout
#print axioms material_theta_dominance_all_of_complex_pole_readout
#assert_central_comparison_axioms material_first_pole_interval_budget
#print axioms material_first_pole_interval_budget
#assert_central_comparison_axioms material_theta_dominance_all_of_separated_readout
#print axioms material_theta_dominance_all_of_separated_readout
end CarryMaterialPoleDominanceComparison

namespace CarryMaterialPoleDominanceComparison
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
example (n : ℕ) : carryMaterialPoleRemainder 0 n = canonicalCompletedNativeLogDerivativeMoment n := by
  simp [carryMaterialPoleRemainder]
example :
    ‖(((20 : ℂ)+Complex.I/2)^2)⁻¹‖ ≤ (1/400 : ℝ) ∧
      (99/100 : ℝ)*‖(((20 : ℂ)+Complex.I/2)^2)⁻¹‖^2 ≤
        (((((20 : ℂ)+Complex.I/2)^2)⁻¹)^2).re := by
  apply material_reciprocal_squared_strip_budget
  all_goals norm_num [Complex.div_re,Complex.div_im]
example : normalizedCompletedNativeEvenFormalSeries =
    CarrySelfAdjointOperator.ProjectiveValve.projectiveValveMass
      (-(PowerSeries.mk canonicalCompletedNativeLogDerivativeMoment)) := by
  have he : carryMaterialPoleRemainder 0 = canonicalCompletedNativeLogDerivativeMoment := by
    funext n
    simp [carryMaterialPoleRemainder]
  simpa only [he,map_zero,zero_mul,sub_zero,one_mul] using
    material_source_formal_deflation 0
end CarryMaterialPoleDominanceComparison


namespace CarryMaterialThetaTailComparison
open CarrySelfAdjointOperator XiThetaScore MeasureTheory Set Filter Polynomial
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem mode_factor (n : ℕ) (u : ℝ) :
    nativeThetaModeWeight n u =
      (8*Real.pi^2*((n+1 : ℕ) : ℝ)^4*Real.exp ((9/2 : ℝ)*u) -
        12*Real.pi*((n+1 : ℕ) : ℝ)^2*Real.exp ((5/2 : ℝ)*u)) *
        Real.exp (-Real.pi*((n+1 : ℕ) : ℝ)^2*Real.exp (2*u)) := by
  unfold nativeThetaModeWeight atom
  ring

private theorem first_mode_lower {u : ℝ} (hu : 0 ≤ u) :
    4*Real.pi^2*Real.exp ((9/2 : ℝ)*u)*Real.exp (-Real.pi*Real.exp (2*u)) ≤
      nativeThetaModeWeight 0 u := by
  rw [mode_factor]
  norm_num only [Nat.cast_one, zero_add, one_pow, mul_one]
  have he : Real.exp ((5/2 : ℝ)*u) ≤ Real.exp ((9/2 : ℝ)*u) :=
    Real.exp_le_exp.mpr (by linarith)
  have hp : 12*Real.pi ≤ 4*Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hm := mul_le_mul hp he (Real.exp_pos _).le (by positivity : 0 ≤ 4*Real.pi^2)
  exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le

private theorem exp_five_ge_sixtyFour : (64 : ℝ) ≤ Real.exp 5 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A bound on each original theta mode by the first original mode.
The constant is an estimate, not a rescaling of the source. -/
theorem material_theta_mode_gaussian (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaModeWeight n u ≤
      2*Real.exp (-3*(n : ℝ)^2-2*(n : ℝ))*nativeThetaModeWeight 0 u := by
  let j : ℝ := n
  let v : ℝ := Real.exp (2*u)
  let A : ℝ := Real.exp ((9/2 : ℝ)*u)*Real.exp (-Real.pi*v)
  have hj : 0 ≤ j := Nat.cast_nonneg n
  have hv : 1 ≤ v := Real.one_le_exp (by linarith)
  have hA : 0 < A := by dsimp [A]; positivity
  have he : (j+1)^4 ≤ Real.exp (4*j) := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ j+1) (Real.add_one_le_exp j) 4
    calc
      _ ≤ (Real.exp j)^4 := h
      _ = _ := (Real.exp_nat_mul j 4).symm
  have hgap : Real.exp (-Real.pi*((j+1)^2-1)*v) ≤ Real.exp (-3*((j+1)^2-1)) := by
    apply Real.exp_le_exp.mpr
    have hs : 0 ≤ (j+1)^2-1 := by nlinarith
    have hp := mul_le_mul Real.pi_gt_three.le hv (by positivity : (0 : ℝ) ≤ 1) Real.pi_pos.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) hs]
  have hdecay : (j+1)^4*Real.exp (-Real.pi*((j+1)^2-1)*v) ≤ Real.exp (-3*j^2-2*j) := by
    calc
      _ ≤ Real.exp (4*j)*Real.exp (-3*((j+1)^2-1)) :=
        mul_le_mul he hgap (Real.exp_pos _).le (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsplit : Real.exp (-Real.pi*(j+1)^2*v) =
      Real.exp (-Real.pi*((j+1)^2-1)*v)*Real.exp (-Real.pi*v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hupper : nativeThetaModeWeight n u ≤
      8*Real.pi^2*((j+1)^4*Real.exp (-Real.pi*((j+1)^2-1)*v))*A := by
    rw [mode_factor]
    push_cast
    change (8*Real.pi^2*(j+1)^4*Real.exp ((9/2 : ℝ)*u) -
      12*Real.pi*(j+1)^2*Real.exp ((5/2 : ℝ)*u))*Real.exp (-Real.pi*(j+1)^2*v) ≤ _
    rw [hsplit]
    dsimp [A]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 12*Real.pi*(j+1)^2*Real.exp ((5/2 : ℝ)*u))
      (by positivity : 0 ≤ Real.exp (-Real.pi*((j+1)^2-1)*v)*Real.exp (-Real.pi*v))]
  calc
    _ ≤ 8*Real.pi^2*((j+1)^4*Real.exp (-Real.pi*((j+1)^2-1)*v))*A := hupper
    _ ≤ 8*Real.pi^2*Real.exp (-3*j^2-2*j)*A := by gcongr
    _ = 2*Real.exp (-3*j^2-2*j)*(4*Real.pi^2*A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [A, v, mul_assoc] using first_mode_lower hu) (by positivity)

private theorem gaussian_shift_bound (j K : ℕ) :
    Real.exp (-3*((j+K : ℕ) : ℝ)^2-2*((j+K : ℕ) : ℝ)) ≤
      (1/64 : ℝ)^j*Real.exp (-3*(K : ℝ)^2-2*(K : ℝ)) := by
  have hj : (j : ℝ) ≤ (j : ℝ)^2 := by
    norm_cast
    simpa only [pow_two] using Nat.le_mul_self j
  have he : Real.exp (-5*(j : ℝ)) ≤ (1/64 : ℝ)^j := by
    rw [show -5*(j : ℝ) = (j : ℝ)*(-5) by ring, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 64)).2 exp_five_ge_sixtyFour
  calc
    _ ≤ Real.exp (-5*(j : ℝ)+(-3*(K : ℝ)^2-2*(K : ℝ))) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (Nat.cast_nonneg (α := ℝ) K)]
    _ = Real.exp (-5*(j : ℝ))*Real.exp (-3*(K : ℝ)^2-2*(K : ℝ)) := Real.exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le

/-- Geometric corollary of the stronger Gaussian source-mode bound. -/
theorem material_theta_mode_geometric (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaModeWeight n u ≤ 2*(1/64 : ℝ)^n*nativeThetaModeWeight 0 u := by
  have he := gaussian_shift_bound n 0
  norm_num only [Nat.add_zero, Nat.cast_zero, zero_pow (by omega : (2 : ℕ) ≠ 0),
    mul_zero, sub_zero, neg_zero, Real.exp_zero, mul_one] at he
  exact (material_theta_mode_gaussian n hu).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num))
      (nativeThetaModeWeight_pos 0 hu).le)

/-- Relative error budget for a finite prefix of the UNCHANGED source. -/
def materialThetaTailBudget (K : ℕ) : ℝ :=
  (128/63 : ℝ)*Real.exp (-3*(K : ℝ)^2-2*(K : ℝ))

theorem material_theta_first_mode_le_full {u : ℝ} (hu : 0 ≤ u) :
    nativeThetaModeWeight 0 u ≤ completedNativeXiCosineKernel u := by
  rw [← nativeThetaModeWeight_tsum]
  exact (nativeThetaModeWeight_summable u).le_tsum 0 (fun n _ => (nativeThetaModeWeight_pos n hu).le)

/-- The omitted infinite series is retained as a nonnegative defect. -/
theorem material_theta_prefix_defect (K : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ completedNativeXiCosineKernel u-nativeThetaPrefixWeight K u ∧
      completedNativeXiCosineKernel u-nativeThetaPrefixWeight K u ≤
        materialThetaTailBudget K*completedNativeXiCosineKernel u := by
  have hs := nativeThetaModeWeight_summable u
  have hsplit := hs.sum_add_tsum_nat_add K
  rw [nativeThetaModeWeight_tsum] at hsplit
  have heq : completedNativeXiCosineKernel u-nativeThetaPrefixWeight K u =
      ∑' j : ℕ, nativeThetaModeWeight (j+K) u := by
    change completedNativeXiCosineKernel u - (∑ j ∈ Finset.range K, nativeThetaModeWeight j u) = _
    linarith
  constructor
  · rw [heq]
    exact tsum_nonneg (fun j => (nativeThetaModeWeight_pos (j+K) hu).le)
  · rw [heq]
    have hsum : (∑' j : ℕ, nativeThetaModeWeight (j+K) u) ≤
        ∑' j : ℕ, (1/64 : ℝ)^j*(2*Real.exp (-3*(K : ℝ)^2-2*(K : ℝ))*nativeThetaModeWeight 0 u) := by
      apply Summable.tsum_le_tsum
      · intro j
        exact (material_theta_mode_gaussian (j+K) hu).trans (by
          have he := gaussian_shift_bound j K
          nlinarith [mul_le_mul_of_nonneg_right he (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
            (nativeThetaModeWeight_pos 0 hu).le)])
      · exact hs.comp_injective (fun a b h => Nat.add_right_cancel h)
      · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/64)
          (by norm_num : (1/64 : ℝ) < 1)).mul_right _
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/64)
      (by norm_num : (1/64 : ℝ) < 1)] at hsum
    have hc : (1-(1/64 : ℝ))⁻¹*(2*Real.exp (-3*(K : ℝ)^2-2*(K : ℝ))*nativeThetaModeWeight 0 u) =
        materialThetaTailBudget K*nativeThetaModeWeight 0 u := by
      unfold materialThetaTailBudget
      norm_num
      ring
    rw [hc] at hsum
    exact hsum.trans (mul_le_mul_of_nonneg_left (material_theta_first_mode_le_full hu) (by
      unfold materialThetaTailBudget; positivity))

theorem material_theta_prefix_between (K : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ nativeThetaPrefixWeight K u ∧
      nativeThetaPrefixWeight K u ≤ completedNativeXiCosineKernel u := by
  refine ⟨Finset.sum_nonneg (fun n _ => (nativeThetaModeWeight_pos n hu).le), ?_⟩
  exact sub_nonneg.mp (material_theta_prefix_defect K hu).1

theorem material_theta_prefix_continuous (K : ℕ) : Continuous (nativeThetaPrefixWeight K) := by
  unfold nativeThetaPrefixWeight
  exact continuous_finsetSum _ (fun n _ =>
    continuous_iff_continuousAt.mpr (fun u => (nativeThetaModeWeight_hasDerivAt n u).continuousAt))

theorem material_theta_prefix_integrable (P : ℝ[X]) (K : ℕ) :
    IntegrableOn (fun u : ℝ => P.eval u*nativeThetaPrefixWeight K u) (Ioi 0) := by
  apply (integrableOn_polynomial_mul_nativeXiKernel P).norm.mono'
  · exact (P.continuous.mul (material_theta_prefix_continuous K)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (material_theta_prefix_between K hu.le).1,
      abs_of_pos (completedNativeXiCosineKernel_pos hu.le)]
    exact mul_le_mul_of_nonneg_left (material_theta_prefix_between K hu.le).2 (abs_nonneg _)

/-- A readout of a finite modal prefix; the physical source remains full. -/
def materialThetaPrefixIntegral (P : ℝ[X]) (K : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), P.eval u*nativeThetaPrefixWeight K u

/-- Absolute mass of the already synthesized signed source density.
This error budget does not define or change a Hilbert metric. -/
def materialThetaAbsoluteMass (P : ℝ[X]) : ℝ :=
  ∫ u in Ioi (0 : ℝ), ‖P.eval u*completedNativeXiCosineKernel u‖

theorem material_theta_absolute_mass_nonneg (P : ℝ[X]) :
    0 ≤ materialThetaAbsoluteMass P := integral_nonneg (fun _ => norm_nonneg _)

/-- Exact signed remainder before taking any estimate. -/
theorem material_theta_prefix_exact (P : ℝ[X]) (K : ℕ) :
    nativeXiPolynomialIntegral P = materialThetaPrefixIntegral P K +
      ∫ u in Ioi (0 : ℝ), P.eval u*(completedNativeXiCosineKernel u-nativeThetaPrefixWeight K u) := by
  have heq : nativeXiPolynomialIntegral P-materialThetaPrefixIntegral P K =
      ∫ u in Ioi (0 : ℝ), P.eval u*(completedNativeXiCosineKernel u-nativeThetaPrefixWeight K u) := by
    change (∫ u in Ioi (0 : ℝ), P.eval u*completedNativeXiCosineKernel u) -
      (∫ u in Ioi (0 : ℝ), P.eval u*nativeThetaPrefixWeight K u) = _
    rw [← integral_sub (integrableOn_polynomial_mul_nativeXiKernel P)
      (material_theta_prefix_integrable P K)]
    congr 1
    funext u
    ring
  linarith

/-- Signed polynomial cancellations are preserved in the principal integral;
only the size of the omitted modes is bounded in absolute value. -/
theorem material_theta_prefix_error (P : ℝ[X]) (K : ℕ) :
    |nativeXiPolynomialIntegral P-materialThetaPrefixIntegral P K| ≤
      materialThetaTailBudget K*materialThetaAbsoluteMass P := by
  have heq : nativeXiPolynomialIntegral P-materialThetaPrefixIntegral P K =
      ∫ u in Ioi (0 : ℝ), P.eval u*(completedNativeXiCosineKernel u-nativeThetaPrefixWeight K u) := by
    linarith [material_theta_prefix_exact P K]
  rw [heq, ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le
    ((integrableOn_polynomial_mul_nativeXiKernel P).norm.const_mul (materialThetaTailBudget K))
    (show ∀ᵐ u : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      ‖P.eval u*(completedNativeXiCosineKernel u-nativeThetaPrefixWeight K u)‖ ≤
        materialThetaTailBudget K*‖P.eval u*completedNativeXiCosineKernel u‖ by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      obtain ⟨h0,h1⟩ := material_theta_prefix_defect K hu.le
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0,
        abs_of_pos (completedNativeXiCosineKernel_pos hu.le)]
      nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (P.eval u))])
  simpa only [integral_const_mul, materialThetaAbsoluteMass] using h

theorem material_theta_tail_budget_tendsto_zero :
    Tendsto materialThetaTailBudget atTop (nhds 0) := by
  apply squeeze_zero (g := fun K : ℕ => (128/63 : ℝ)*(1/64 : ℝ)^K)
  · intro K
    unfold materialThetaTailBudget
    positivity
  · intro K
    have he := gaussian_shift_bound K 0
    norm_num only [Nat.add_zero, Nat.cast_zero, zero_pow (by omega : (2 : ℕ) ≠ 0),
      mul_zero, sub_zero, neg_zero, Real.exp_zero, mul_one] at he
    exact mul_le_mul_of_nonneg_left he (by norm_num)
  · simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/64)
        (by norm_num : (1/64 : ℝ) < 1)).const_mul (128/63 : ℝ)

/-- Integrated convergence for every synthesized polynomial, proved from
the actual infinite-mode bound, without an exchange of unjustified limits. -/
theorem material_theta_prefix_integral_tendsto (P : ℝ[X]) :
    Tendsto (materialThetaPrefixIntegral P) atTop (nhds (nativeXiPolynomialIntegral P)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (g := fun K => materialThetaTailBudget K*materialThetaAbsoluteMass P)
  · intro K
    exact norm_nonneg _
  · intro K
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact material_theta_prefix_error P K
  · simpa only [zero_mul] using
      material_theta_tail_budget_tendsto_zero.mul_const (materialThetaAbsoluteMass P)

/-- An exact finite-prefix criterion, not an assumed source positivity.
The bound is necessary as well as sufficient when the cutoff may vary. -/
theorem material_theta_positive_iff_finite_margin (P : ℝ[X]) :
    0 < nativeXiPolynomialIntegral P ↔
      ∃ K : ℕ, materialThetaTailBudget K*materialThetaAbsoluteMass P <
        materialThetaPrefixIntegral P K := by
  constructor
  · intro hpos
    have hbudget : Tendsto (fun K => materialThetaTailBudget K*materialThetaAbsoluteMass P)
        atTop (nhds 0) := by
      simpa only [zero_mul] using
        material_theta_tail_budget_tendsto_zero.mul_const (materialThetaAbsoluteMass P)
    have hgap := (material_theta_prefix_integral_tendsto P).sub hbudget
    simp only [sub_zero] at hgap
    obtain ⟨K,hK⟩ := (hgap.eventually (eventually_gt_nhds hpos)).exists
    exact ⟨K, by linarith⟩
  · rintro ⟨K,hK⟩
    have he := material_theta_prefix_error P K
    have hl := (abs_le.mp he).1
    linarith

/-- A finite coefficient ledger against the original raw theta integrals.
Coefficients are taken after synthesis, including all ordered crosses. -/
def materialThetaCoefficientBudget (P : ℝ[X]) : ℝ :=
  ∑ d ∈ P.support, |P.coeff d| *
    (∫ u in Ioi (0 : ℝ), u^d*completedNativeXiCosineKernel u)

theorem material_theta_absolute_mass_le_coefficient_budget (P : ℝ[X]) :
    materialThetaAbsoluteMass P ≤ materialThetaCoefficientBudget P := by
  classical
  let Q : ℝ[X] := ∑ d ∈ P.support, Polynomial.monomial d |P.coeff d|
  have hQ : nativeXiPolynomialIntegral Q = materialThetaCoefficientBudget P := by
    simp only [Q, map_sum, materialThetaCoefficientBudget]
    apply Finset.sum_congr rfl
    intro d hd
    change (∫ u in Ioi (0 : ℝ), (Polynomial.monomial d |P.coeff d|).eval u*
      completedNativeXiCosineKernel u) = _
    simp only [Polynomial.eval_monomial, mul_assoc, integral_const_mul]
  rw [← hQ]
  apply integral_mono_ae (integrableOn_polynomial_mul_nativeXiKernel P).norm
    (integrableOn_polynomial_mul_nativeXiKernel Q)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have heval : |P.eval u| ≤ Q.eval u := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum]
    calc
      _ ≤ ∑ d ∈ P.support, |P.coeff d*u^d| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
          abs_mul, abs_pow, abs_of_nonneg (show 0 ≤ u from le_of_lt hu)]
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (completedNativeXiCosineKernel_pos hu.le)]
  exact mul_le_mul_of_nonneg_right heval (completedNativeXiCosineKernel_pos hu.le).le

theorem material_theta_coefficient_budget_nonneg (P : ℝ[X]) :
    0 ≤ materialThetaCoefficientBudget P :=
  (material_theta_absolute_mass_nonneg P).trans (material_theta_absolute_mass_le_coefficient_budget P)

theorem material_theta_prefix_coefficient_error (P : ℝ[X]) (K : ℕ) :
    |nativeXiPolynomialIntegral P-materialThetaPrefixIntegral P K| ≤
      materialThetaTailBudget K*materialThetaCoefficientBudget P := by
  exact (material_theta_prefix_error P K).trans
    (mul_le_mul_of_nonneg_left (material_theta_absolute_mass_le_coefficient_budget P)
      (by unfold materialThetaTailBudget; positivity))

theorem material_theta_source_interval (P : ℝ[X]) (K : ℕ) :
    materialThetaPrefixIntegral P K-materialThetaTailBudget K*materialThetaCoefficientBudget P ≤
      nativeXiPolynomialIntegral P ∧
    nativeXiPolynomialIntegral P ≤
      materialThetaPrefixIntegral P K+materialThetaTailBudget K*materialThetaCoefficientBudget P := by
  have he := abs_le.mp (material_theta_prefix_coefficient_error P K)
  constructor <;> linarith [he.1, he.2]

theorem material_theta_positive_iff_coefficient_margin (P : ℝ[X]) :
    0 < nativeXiPolynomialIntegral P ↔
      ∃ K : ℕ, materialThetaTailBudget K*materialThetaCoefficientBudget P <
        materialThetaPrefixIntegral P K := by
  constructor
  · intro hpos
    have hbudget : Tendsto (fun K => materialThetaTailBudget K*materialThetaCoefficientBudget P)
        atTop (nhds 0) := by
      simpa only [zero_mul] using
        material_theta_tail_budget_tendsto_zero.mul_const (materialThetaCoefficientBudget P)
    have hgap := (material_theta_prefix_integral_tendsto P).sub hbudget
    simp only [sub_zero] at hgap
    obtain ⟨K,hK⟩ := (hgap.eventually (eventually_gt_nhds hpos)).exists
    exact ⟨K, by linarith⟩
  · rintro ⟨K,hK⟩
    have hl := (material_theta_source_interval P K).1
    linarith

end
end CarryMaterialThetaTailComparison

namespace CarryMaterialThetaTailComparison
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator Filter
open CarryMaterialNullHierarchyComparison CarryMaterialHierarchySignComparison
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

/-- The literal ordered quadratic source polynomial is synthesized BEFORE
its modal error is estimated. No crosses or Schur correction are removed. -/
theorem material_theta_quadratic_prefix_error (s N K : ℕ) (x : Fin N → ℝ) :
    |sourceMomentQuadratic canonicalCompletedNativeLogDerivativeMoment s N x -
      materialThetaPrefixIntegral (nativeThetaQuadraticPolynomial s N x) K| ≤
      materialThetaTailBudget K*materialThetaCoefficientBudget (nativeThetaQuadraticPolynomial s N x) := by
  rw [← nativeThetaQuadraticPolynomial_integral]
  exact material_theta_prefix_coefficient_error _ K

theorem material_null_theta_prefix_exact (k K : ℕ) :
    carryMaterialNullCoefficient k =
      materialThetaPrefixIntegral (carryMaterialNullThetaPolynomial k) K +
        ∫ u in Set.Ioi (0 : ℝ), (carryMaterialNullThetaPolynomial k).eval u *
          (completedNativeXiCosineKernel u-nativeThetaPrefixWeight K u) := by
  rw [← material_null_theta_integral]
  exact material_theta_prefix_exact _ K

theorem material_null_theta_prefix_error (k K : ℕ) :
    |carryMaterialNullCoefficient k-materialThetaPrefixIntegral (carryMaterialNullThetaPolynomial k) K| ≤
      materialThetaTailBudget K*materialThetaCoefficientBudget (carryMaterialNullThetaPolynomial k) := by
  rw [← material_null_theta_integral]
  exact material_theta_prefix_coefficient_error _ K

/-- A priori K=k+2. This bound is unconditional in EVERY order; it does not
assert that the principal signed integral dominates the displayed error. -/
theorem material_null_theta_adaptive_error (k : ℕ) :
    |carryMaterialNullCoefficient k-materialThetaPrefixIntegral (carryMaterialNullThetaPolynomial k) (k+2)| ≤
      (128/63 : ℝ)*Real.exp (-3*((k+2 : ℕ) : ℝ)^2-2*((k+2 : ℕ) : ℝ))*
        materialThetaCoefficientBudget (carryMaterialNullThetaPolynomial k) :=
  material_null_theta_prefix_error k (k+2)

theorem material_null_theta_prefix_interval (k K : ℕ) :
    materialThetaPrefixIntegral (carryMaterialNullThetaPolynomial k) K -
      materialThetaTailBudget K*materialThetaCoefficientBudget (carryMaterialNullThetaPolynomial k) ≤
        carryMaterialNullCoefficient k ∧
    carryMaterialNullCoefficient k ≤
      materialThetaPrefixIntegral (carryMaterialNullThetaPolynomial k) K +
        materialThetaTailBudget K*materialThetaCoefficientBudget (carryMaterialNullThetaPolynomial k) := by
  rw [← material_null_theta_integral]
  exact material_theta_source_interval _ K

theorem material_null_theta_prefix_tendsto (k : ℕ) :
    Tendsto (materialThetaPrefixIntegral (carryMaterialNullThetaPolynomial k)) atTop
      (nhds (carryMaterialNullCoefficient k)) := by
  rw [← material_null_theta_integral]
  exact material_theta_prefix_integral_tendsto _

theorem material_null_positive_iff_prefix_margin (k : ℕ) :
    0 < carryMaterialNullCoefficient k ↔
      ∃ K : ℕ, materialThetaTailBudget K*materialThetaCoefficientBudget (carryMaterialNullThetaPolynomial k) <
        materialThetaPrefixIntegral (carryMaterialNullThetaPolynomial k) K := by
  rw [← material_null_theta_integral]
  exact material_theta_positive_iff_coefficient_margin _

/-- Exact all-order source criterion. A cutoff and a signed principal
margin for every order remain to be constructed, not assumed proved. -/
theorem material_hierarchy_positive_iff_prefix_margin :
    (∀ k : ℕ, 0 < k → 0 < carryMaterialNullCoefficient k) ↔
      ∀ k : ℕ, 0 < k → ∃ K : ℕ,
        materialThetaTailBudget K*materialThetaCoefficientBudget (carryMaterialNullThetaPolynomial k) <
          materialThetaPrefixIntegral (carryMaterialNullThetaPolynomial k) K := by
  exact forall_congr' (fun k => imp_congr_right (fun _ => material_null_positive_iff_prefix_margin k))

theorem material_null_fixed_family_positive_of_prefix_margin (k K : ℕ) (hk : 0 < k)
    (hmargin : materialThetaTailBudget K*materialThetaCoefficientBudget (carryMaterialNullThetaPolynomial k) <
      materialThetaPrefixIntegral (carryMaterialNullThetaPolynomial k) K)
    {n : ℕ} (c a : Fin n → ℝ)
    (hM : ∀ j, 0 < j → j < k → (∑ i, c i*(a i)^j)=0)
    (hMk : (∑ i, c i*(a i)^k) ≠ 0) :
    ∀ᶠ e : ℝ in nhds 0, e ≠ 0 →
      0 < carryRealKernelEnergy carryMaterialRealResidual c (fun i => e*a i) :=
  material_null_fixed_family_positive k hk
    ((material_null_positive_iff_prefix_margin k).mpr ⟨K,hmargin⟩) c a hM hMk

end
end CarryMaterialThetaTailComparison


namespace CarryMaterialThetaTailComparison
#assert_central_comparison_axioms material_theta_mode_gaussian
#print axioms material_theta_mode_gaussian
#assert_central_comparison_axioms material_theta_mode_geometric
#print axioms material_theta_mode_geometric
#assert_central_comparison_axioms materialThetaTailBudget
#print axioms materialThetaTailBudget
#assert_central_comparison_axioms material_theta_first_mode_le_full
#print axioms material_theta_first_mode_le_full
#assert_central_comparison_axioms material_theta_prefix_defect
#print axioms material_theta_prefix_defect
#assert_central_comparison_axioms material_theta_prefix_between
#print axioms material_theta_prefix_between
#assert_central_comparison_axioms material_theta_prefix_continuous
#print axioms material_theta_prefix_continuous
#assert_central_comparison_axioms material_theta_prefix_integrable
#print axioms material_theta_prefix_integrable
#assert_central_comparison_axioms materialThetaPrefixIntegral
#print axioms materialThetaPrefixIntegral
#assert_central_comparison_axioms materialThetaAbsoluteMass
#print axioms materialThetaAbsoluteMass
#assert_central_comparison_axioms material_theta_absolute_mass_nonneg
#print axioms material_theta_absolute_mass_nonneg
#assert_central_comparison_axioms material_theta_prefix_exact
#print axioms material_theta_prefix_exact
#assert_central_comparison_axioms material_theta_prefix_error
#print axioms material_theta_prefix_error
#assert_central_comparison_axioms material_theta_tail_budget_tendsto_zero
#print axioms material_theta_tail_budget_tendsto_zero
#assert_central_comparison_axioms material_theta_prefix_integral_tendsto
#print axioms material_theta_prefix_integral_tendsto
#assert_central_comparison_axioms material_theta_positive_iff_finite_margin
#print axioms material_theta_positive_iff_finite_margin
#assert_central_comparison_axioms materialThetaCoefficientBudget
#print axioms materialThetaCoefficientBudget
#assert_central_comparison_axioms material_theta_absolute_mass_le_coefficient_budget
#print axioms material_theta_absolute_mass_le_coefficient_budget
#assert_central_comparison_axioms material_theta_coefficient_budget_nonneg
#print axioms material_theta_coefficient_budget_nonneg
#assert_central_comparison_axioms material_theta_prefix_coefficient_error
#print axioms material_theta_prefix_coefficient_error
#assert_central_comparison_axioms material_theta_source_interval
#print axioms material_theta_source_interval
#assert_central_comparison_axioms material_theta_positive_iff_coefficient_margin
#print axioms material_theta_positive_iff_coefficient_margin
#assert_central_comparison_axioms material_theta_quadratic_prefix_error
#print axioms material_theta_quadratic_prefix_error
#assert_central_comparison_axioms material_null_theta_prefix_exact
#print axioms material_null_theta_prefix_exact
#assert_central_comparison_axioms material_null_theta_prefix_error
#print axioms material_null_theta_prefix_error
#assert_central_comparison_axioms material_null_theta_adaptive_error
#print axioms material_null_theta_adaptive_error
#assert_central_comparison_axioms material_null_theta_prefix_interval
#print axioms material_null_theta_prefix_interval
#assert_central_comparison_axioms material_null_theta_prefix_tendsto
#print axioms material_null_theta_prefix_tendsto
#assert_central_comparison_axioms material_null_positive_iff_prefix_margin
#print axioms material_null_positive_iff_prefix_margin
#assert_central_comparison_axioms material_hierarchy_positive_iff_prefix_margin
#print axioms material_hierarchy_positive_iff_prefix_margin
#assert_central_comparison_axioms material_null_fixed_family_positive_of_prefix_margin
#print axioms material_null_fixed_family_positive_of_prefix_margin
end CarryMaterialThetaTailComparison

namespace CarryMaterialThetaTailComparison
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator Polynomial
open CarryMaterialHierarchySignComparison
noncomputable section

-- Empty and one-mode cutoffs test the zero-based modal conventions.
example (P : ℝ[X]) : materialThetaPrefixIntegral P 0 = 0 := by
  simp [materialThetaPrefixIntegral, nativeThetaPrefixWeight]

example (u : ℝ) : nativeThetaPrefixWeight 1 u = nativeThetaModeWeight 0 u := by
  simp [nativeThetaPrefixWeight]

example : materialThetaTailBudget 0 = (128/63 : ℝ) := by
  norm_num [materialThetaTailBudget]

-- The actual even-source cross coefficient is preserved literally.
example : carryMaterialNullThetaPolynomial 2 =
    nativeThetaMomentPolynomial 2 -
      (2*canonicalCompletedNativeLogDerivativeMoment 1/canonicalCompletedNativeLogDerivativeMoment 0) •
        nativeThetaMomentPolynomial 1 +
      (canonicalCompletedNativeLogDerivativeMoment 1/canonicalCompletedNativeLogDerivativeMoment 0)^2 •
        nativeThetaMomentPolynomial 0 := material_null_theta_even 1

-- Established source signs imply existence of certified modal margins.
-- This does not provide numerical cutoffs or a new sign for order seven.
example (k : ℕ) (hk : 0 < k) (hk6 : k ≤ 6) :
    ∃ K : ℕ, materialThetaTailBudget K*materialThetaCoefficientBudget (carryMaterialNullThetaPolynomial k) <
      materialThetaPrefixIntegral (carryMaterialNullThetaPolynomial k) K :=
  (material_null_positive_iff_prefix_margin k).mp
    (material_null_coefficient_pos_through_six k hk hk6)

end
end CarryMaterialThetaTailComparison

namespace CarryMaterialClockCouplingComparison
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryMaterialGreenPairComparison
open Filter
open scoped Topology ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The actual coupled-clock ledger, with the readout-hidden Green return
subtracted ONLY after the central/complement and forcing synthesis. The
canonical residual is the same source-defined residual as before. No sign
or positive Hilbert representation is assumed. -/
theorem material_clock_canonical_residual_ledger :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U,
      (carryMaterialPairGreen
          (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t))
          (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair u)) +
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
          (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) +
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
          (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) +
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
          (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) +
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
          (carryMaterialPairReduction u (carryMaterialClockForcingPair u))) -
        carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
          (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) =
      (2 : ℂ)*((carryMaterialResponseScale^2*t*u : ℝ) : ℂ)*
        conj (baseTwoCanonicalResponse t)*baseTwoCanonicalResponse u*((u-t : ℝ) : ℂ)*
          (conj (carryMaterialNormalizedResponse t)*carryMaterialNormalizedResponse u *
            dslope carryMaterialReducedResponse t u) := by
  obtain ⟨U,hU,h0,h⟩ := material_reduced_pair_canonical_residual_numerator
  refine ⟨U,hU,h0,?_⟩
  intro t ht u hu
  have he := h t ht u hu
  rw [carryMaterialClock_reduced_green_ledger] at he
  exact he

/-- Exact central-row cancellation in the physical source. Orthogonal
central projection and the seed/return readout projection are distinct.
The hidden Green balance is not discarded as an unobserved coordinate. -/
theorem material_clock_first_row_hidden_balance (u : ℝ) :
    carryMaterialPairGreen
      (carryMaterialPairComplement (carryMaterialReducedCompanionPair 0))
      (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) =
      carryMaterialPairGreen
        (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair 0))
        (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair u)) +
      carryMaterialPairGreen (carryMaterialPairReduction 0 (carryMaterialClockForcingPair 0))
        (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) +
      carryMaterialPairGreen (carryMaterialPairReduction 0 (carryMaterialClockForcingPair 0))
        (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) := by
  have h := carryMaterialPairGreen_readout_ledger
    (carryMaterialReducedCompanionPair 0) (carryMaterialReducedCompanionPair u)
  rw [material_reduced_pair_center_invisible_nonzero.1] at h
  have hscalar : carryMaterialPairGreen (0 : ℂ × ℂ)
      (carryMaterialPairReadout (carryMaterialReducedCompanionPair u)) = 0 := by
    simp [carryMaterialPairGreen]
  rw [hscalar, mul_zero, zero_add] at h
  have hzero (x : MaterialCarrier × MaterialCarrier) :
      carryMaterialPairGreen (0 : MaterialCarrier × MaterialCarrier) x = 0 := by
    simp [carryMaterialPairGreen]
  rw [carryMaterialClock_reduced_green_ledger] at h
  have hc : carryMaterialPairReduction 0 (carryMaterialClockCompressedPair 0) = 0 := by
    rw [carryMaterialClock_compressed_pair_origin, map_zero]
  rw [hc,hzero,hzero,add_zero,add_zero] at h
  exact h.symm

/-- The same coupled physical ledger reaches the REAL canonical residual.
The complex notation retains the two original quadratures and phases. -/
theorem material_clock_real_residual_numerator :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U,
      (carryMaterialPairGreen
          (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair t))
          (carryMaterialCentralPairProjection (carryMaterialReducedCompanionPair u)) +
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
          (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) +
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockCompressedPair t))
          (carryMaterialPairReduction u (carryMaterialClockForcingPair u)) +
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
          (carryMaterialPairReduction u (carryMaterialClockCompressedPair u)) +
        carryMaterialPairGreen (carryMaterialPairReduction t (carryMaterialClockForcingPair t))
          (carryMaterialPairReduction u (carryMaterialClockForcingPair u))) -
        carryMaterialPairGreen (carryMaterialPairComplement (carryMaterialReducedCompanionPair t))
          (carryMaterialPairComplement (carryMaterialReducedCompanionPair u)) =
      (2 : ℂ)*((carryMaterialResponseScale^2*t*u : ℝ) : ℂ)*
        conj (baseTwoCanonicalResponse t)*baseTwoCanonicalResponse u*((u-t : ℝ) : ℂ)*
          (carryMaterialRealResidual t u : ℂ) := by
  obtain ⟨U,hU,h0,h⟩ := material_clock_canonical_residual_ledger
  refine ⟨U,hU,h0,?_⟩
  intro t ht u hu
  rw [CarryMaterialPositiveResidualComparison.material_real_residual_coe]
  exact h t ht u hu

end
end CarryMaterialClockCouplingComparison

namespace CarryMaterialClockCouplingComparison
#assert_central_comparison_axioms material_clock_canonical_residual_ledger
#print axioms material_clock_canonical_residual_ledger
#assert_central_comparison_axioms material_clock_first_row_hidden_balance
#print axioms material_clock_first_row_hidden_balance
#assert_central_comparison_axioms material_clock_real_residual_numerator
#print axioms material_clock_real_residual_numerator
end CarryMaterialClockCouplingComparison

namespace CarryMaterialValveGlobalReturnComparison
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator CarryMaterialClockCouplingComparison
open scoped Topology ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Literal calibration with the original Wronskian: its arguments are u,t,
as in the existing physical-pair theorem, never silently reversed. -/
theorem material_valve_return_green_wronskian (eta : ℝ) (heta : eta ≠ 0) (t u : ℝ) :
    carryValveReturnGreen eta t u =
      completedGreenWronskian completedNativeOperatorCharacteristic completedNativeOperatorBoundaryCompanion
        (u : ℂ) (t : ℂ) := by
  rw [← carryValveReturnGreen_physical_ledger eta heta]
  exact CarryMaterialGreenPairComparison.material_pair_corrected_green t u

/-- The whole-cell ordinary/clocked return expression reaches the *same*
six-term signed balance of PR #16, including its hidden complement. This
does not prove the sign of the normalized real residual. -/
theorem material_valve_global_residual_numerator (eta : ℝ) (heta : eta ≠ 0) :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U,
      carryValveReducedReturnBalance eta t u =
        (2 : ℂ) * ((carryMaterialResponseScale^2*t*u : ℝ) : ℂ) *
          conj (baseTwoCanonicalResponse t) * baseTwoCanonicalResponse u * ((u-t : ℝ) : ℂ) *
            (carryMaterialRealResidual t u : ℂ) := by
  obtain ⟨U,hU,h0,h⟩ := material_clock_real_residual_numerator
  refine ⟨U,hU,h0,?_⟩
  intro t ht u hu
  have he := h t ht u hu
  rw [← carryMaterialClock_reduced_green_ledger,
    carryValveReducedReturnBalance_physical eta heta] at he
  exact he

/-- The full balance cancels on its central row before any normalization.
This uses the source's actual zero companion readout and keeps the hidden
Green subtraction; it is not a proof that either physical term vanishes. -/
theorem material_valve_global_central_row (eta : ℝ) (heta : eta ≠ 0) (u : ℝ) :
    carryValveReducedReturnBalance eta 0 u = 0 := by
  rw [carryValveReducedReturnBalance]
  have hc : carryValveCompanionReadout eta 0 = 0 := by
    rw [carryValveCompanionReadout_eq eta heta]
    exact CarryMaterialGreenPairComparison.material_companion_center_readout_zero
  simp only [hc, zero_mul, mul_zero, Complex.ofReal_zero, map_zero, sub_zero]

/-- The paired cutoff limit reaches the full canonical residual numerator,
with the scale and response of the full source fixed throughout the limit. -/
theorem material_valve_prefix_residual_limit (eta : ℝ) (heta : eta ≠ 0) :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∀ t ∈ U, ∀ u ∈ U,
      Filter.Tendsto (fun p : ℕ × ℕ => carryValvePrefixReducedBalance eta p.1 p.2 t u)
        (Filter.atTop ×ˢ Filter.atTop)
        (nhds ((2 : ℂ) * ((carryMaterialResponseScale^2*t*u : ℝ) : ℂ) *
          conj (baseTwoCanonicalResponse t) * baseTwoCanonicalResponse u * ((u-t : ℝ) : ℂ) *
            (carryMaterialRealResidual t u : ℂ))) := by
  obtain ⟨U,hU,h0,h⟩ := material_valve_global_residual_numerator eta heta
  refine ⟨U,hU,h0,?_⟩
  intro t ht u hu
  rw [← h t ht u hu]
  exact carryValvePrefixReducedBalance_tendsto eta heta t u

end
end CarryMaterialValveGlobalReturnComparison

namespace CarryMaterialValveGlobalReturnComparison
#assert_central_comparison_axioms material_valve_return_green_wronskian
#print axioms material_valve_return_green_wronskian
#assert_central_comparison_axioms material_valve_global_residual_numerator
#print axioms material_valve_global_residual_numerator
#assert_central_comparison_axioms material_valve_global_central_row
#print axioms material_valve_global_central_row
#assert_central_comparison_axioms material_valve_prefix_residual_limit
#print axioms material_valve_prefix_residual_limit
end CarryMaterialValveGlobalReturnComparison

namespace CarryMaterialMixedSchurComparison
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarrySelfAdjointOperator CarrySelfAdjointOperator.SourcePositiveReduction
open CarryMaterialResponseComparison CarryMaterialResidualComparison
open CarryMaterialPositiveResidualComparison CarryMaterialThirdNullComparison
open CarryMaterialNullHierarchyComparison CarryMaterialValveGlobalReturnComparison
open scoped Topology ComplexConjugate Matrix
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

local notation "h" => canonicalCompletedNativeLogDerivativeMoment

/-- Scalar analyticity after synthesis, obtained from the existing actual
source germ. No differentiability of the global Hilbert state is assumed. -/
theorem material_response_real_analytic : AnalyticAt ℝ carryMaterialNormalizedResponse 0 := by
  have hc : AnalyticAt ℝ (fun t : ℝ => sourceResponse (t : ℂ)) 0 :=
    AnalyticAt.comp_of_eq (g := sourceResponse) (f := fun t : ℝ => (t : ℂ))
      (x := 0) (y := 0) (sourceResponse_analyticAt_zero.restrictScalars (𝕜 := ℝ))
      (Complex.ofRealCLM.analyticAt 0) rfl
  exact hc.congr material_source_response_eventually_eq.symm

/-- These are mixed confluent observations of the ACTUAL residual, derived
from its completed-source identity. The equality is not used as a definition. -/
theorem material_residual_complex_jet_source (p q : ℕ) :
    carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) p q =
      completedNativeGreenResponseTaylorCoefficient (p+q+1)-
        completedNativeGreenResponseTaylorCoefficient (p+1)*
          completedNativeGreenResponseTaylorCoefficient (q+1)/(h 0 : ℂ) := by
  obtain ⟨U,hU,h0,hR⟩ := material_residual_centered_kernel
  have he := carryKernelJet_germ (K := fun t u => (carryMaterialRealResidual t u : ℂ))
    (L := fun t u => dslope carryMaterialNormalizedResponse t u-
      dslope carryMaterialNormalizedResponse 0 t*dslope carryMaterialNormalizedResponse 0 u/
        (carryMaterialResponseScale : ℂ)) (by
      filter_upwards [hU.mem_nhds h0] with u hu
      filter_upwards [hU.mem_nhds h0] with t ht
      exact hR t ht u hu) p q
  rw [he,carryKernelJet_centered material_response_real_analytic]
  change carryMaterialTaylorShift (p+q+1) 0-
    carryMaterialTaylorShift (p+1) 0*carryMaterialTaylorShift (q+1) 0/
      (carryMaterialResponseScale : ℂ) = _
  rw [material_taylor_shift_center,material_taylor_shift_center,material_taylor_shift_center,
    material_scale_eq]

theorem material_residual_jet_source (p q : ℕ) :
    carryMaterialResidualJet p q =
      (completedNativeGreenResponseTaylorCoefficient (p+q+1)-
        completedNativeGreenResponseTaylorCoefficient (p+1)*
          completedNativeGreenResponseTaylorCoefficient (q+1)/(h 0 : ℂ)).re :=
  congrArg Complex.re (material_residual_complex_jet_source p q)

theorem material_residual_complex_jet_even_even (i j : ℕ) :
    carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) (2*i) (2*j) =
      ((h (i+j)-h i*h j/h 0 : ℝ) : ℂ) := by
  rw [material_residual_complex_jet_source,show 2*i+2*j+1=2*(i+j)+1 by omega,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  push_cast
  rfl

theorem material_residual_jet_even_even (i j : ℕ) :
    carryMaterialResidualJet (2*i) (2*j) = h (i+j)-h i*h j/h 0 := by
  rw [material_residual_jet_source,show 2*i+2*j+1=2*(i+j)+1 by omega,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  norm_cast

theorem material_residual_jet_odd_odd (i j : ℕ) :
    carryMaterialResidualJet (2*i+1) (2*j+1) = h (i+j+1) := by
  rw [material_residual_jet_source,show 2*i+1+(2*j+1)+1=2*(i+j+1)+1 by omega,
    completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
    show 2*i+1+1=2*(i+1) by omega,
    completedNativeGreenResponseTaylorCoefficient_even_eq_zero]
  simp

theorem material_residual_jet_even_odd (i j : ℕ) :
    carryMaterialResidualJet (2*i) (2*j+1) = 0 := by
  rw [material_residual_jet_source,show 2*i+(2*j+1)+1=2*(i+j+1) by omega,
    completedNativeGreenResponseTaylorCoefficient_even_eq_zero,
    show 2*j+1+1=2*(j+1) by omega,
    completedNativeGreenResponseTaylorCoefficient_even_eq_zero]
  simp

theorem material_residual_jet_odd_even (i j : ℕ) :
    carryMaterialResidualJet (2*i+1) (2*j) = 0 := by
  rw [material_residual_jet_source,show 2*i+1+2*j+1=2*(i+j+1) by omega,
    completedNativeGreenResponseTaylorCoefficient_even_eq_zero,
    show 2*i+1+1=2*(i+1) by omega,
    completedNativeGreenResponseTaylorCoefficient_even_eq_zero]
  simp

theorem material_mixed_entries :
    carryMaterialResidualJet 2 2 = h 2-h 1^2/h 0 ∧
    carryMaterialResidualJet 2 4 = h 3-h 1*h 2/h 0 ∧
    carryMaterialResidualJet 4 2 = h 3-h 1*h 2/h 0 ∧
    carryMaterialResidualJet 4 4 = h 4-h 2^2/h 0 := by
  have h11 := material_residual_jet_even_even 1 1
  have h12 := material_residual_jet_even_even 1 2
  have h21 := material_residual_jet_even_even 2 1
  have h22 := material_residual_jet_even_even 2 2
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at h11 h12 h21 h22
  exact ⟨by simpa only [pow_two] using h11,h12,by simpa only [mul_comm] using h21,
    by simpa only [pow_two] using h22⟩

theorem material_mixed_first_pivot_pos : 0 < carryMaterialResidualJet 2 2 := by
  rw [material_mixed_entries.1]
  have he : h 2-h 1^2/h 0=(h 0*h 2-h 1^2)/h 0 := by
    field_simp [canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne']
  rw [he]
  exact div_pos nativeMoment_first_discriminant_pos canonicalCompletedNativeLogDerivativeMoment_zero_pos

theorem material_mixed_pivot_eq :
    carryMaterialMixedPivot = h 4-h 2^2/h 0-
      (h 3-h 1*h 2/h 0)^2/(h 2-h 1^2/h 0) := by
  rw [carryMaterialMixedPivot,material_mixed_entries.1,material_mixed_entries.2.1,
    material_mixed_entries.2.2.1,material_mixed_entries.2.2.2]
  ring

theorem material_third_schur_eq : sourceMomentSchur h 0 2 = h 4-h 2^2/h 0-
    (h 3-h 1*h 2/h 0)^2/(h 2-h 1^2/h 0) := by
  let A := sourceMomentMatrix h 0 2
  let b := sourceMomentCoupling h 0 2
  let delta := h 0*h 2-h 1^2
  have hd : delta ≠ 0 := nativeMoment_first_discriminant_pos.ne'
  have hdet : IsUnit A.det := by
    apply isUnit_iff_ne_zero.mpr
    simpa [A,delta,sourceMomentMatrix,Matrix.det_fin_two,pow_two] using hd
  let v : Fin 2 → ℝ := ![(h 2^2-h 1*h 3)/delta,(h 0*h 3-h 1*h 2)/delta]
  have hv : A *ᵥ v = b := by
    ext i
    fin_cases i <;> simp [A,b,v,sourceMomentMatrix,sourceMomentCoupling,Matrix.mulVec,
      dotProduct,Fin.sum_univ_two]
    all_goals field_simp [hd]; dsimp [delta]; ring
  have hi : A⁻¹ *ᵥ b = v := by
    rw [← hv,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hdet,Matrix.one_mulVec]
  change h 4-b ⬝ᵥ (A⁻¹ *ᵥ b) = _
  rw [hi]
  simp only [b,v,dotProduct,Fin.sum_univ_two,sourceMomentCoupling,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have h0 : h 0 ≠ 0 := canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
  have hp : h 2-h 1^2/h 0 ≠ 0 := by
    intro hz
    apply hd
    dsimp [delta]
    field_simp [h0] at hz
    nlinarith
  dsimp [delta] at hd ⊢
  field_simp [h0,hd,hp]
  field_simp [hd]
  ring


/-- The mixed material direction is the genuine third ordinary Schur pivot. -/
theorem material_mixed_pivot_eq_schur :
    carryMaterialMixedPivot = sourceMomentSchur h 0 2 := by
  rw [material_mixed_pivot_eq,material_third_schur_eq]

/-- Literal source theta normalization, without a sign conclusion. -/
theorem material_mixed_pivot_theta :
    completedNativeRealEvenCharacteristicCoefficient 0*carryMaterialMixedPivot =
      nativeXiPolynomialIntegral (nativeSchurThetaPolynomial 0 2) := by
  rw [nativeSchurThetaPolynomial_integral,nativeSourceSchurRemainder_eq,
    material_mixed_pivot_eq_schur]

theorem material_third_schur_ratio : sourceMomentSchur h 0 2 =
    nativeSourceFiveEvenDiscriminant/(8*(h 0*h 2-h 1^2)) := by
  rw [material_third_schur_eq]
  unfold nativeSourceFiveEvenDiscriminant
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical]
  have h0 : h 0 ≠ 0 := canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
  have hd : h 0*h 2-h 1^2 ≠ 0 := nativeMoment_first_discriminant_pos.ne'
  have hp : h 2-h 1^2/h 0 ≠ 0 := by
    intro hz
    field_simp [h0] at hz
    exact hd (by nlinarith)
  field_simp [h0,hd,hp]
  field_simp [hd]
  ring


/-- Existing theta source sign, reused through the exact mixed crosswalk. -/
theorem material_mixed_pivot_pos : 0 < carryMaterialMixedPivot := by
  rw [material_mixed_pivot_eq_schur,material_third_schur_ratio]
  exact div_pos nativeSourceFiveEvenDiscriminant_pos
    (mul_pos (by norm_num) nativeMoment_first_discriminant_pos)

theorem material_mixed_cross_dominance :
    carryMaterialResidualJet 2 4^2 < carryMaterialResidualJet 2 2*carryMaterialResidualJet 4 4 := by
  have hs : carryMaterialResidualJet 4 2 = carryMaterialResidualJet 2 4 := by
    rw [material_mixed_entries.2.2.1,material_mixed_entries.2.1]
  have hp := material_mixed_pivot_pos
  rw [carryMaterialMixedPivot,hs] at hp
  have hh := (div_lt_iff₀ material_mixed_first_pivot_pos).mp (sub_pos.mp hp)
  simpa only [pow_two,mul_comm] using hh

theorem material_mixed_block_pos (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < carryMaterialMixedBlock x y x y := by
  have hs : carryMaterialResidualJet 4 2 = carryMaterialResidualJet 2 4 := by
    rw [material_mixed_entries.2.2.1,material_mixed_entries.2.1]
  rw [carryMaterialMixedBlock_sewing material_mixed_first_pivot_pos.ne',hs]
  have he : carryMaterialResidualJet 2 2*
      (x+carryMaterialResidualJet 2 4/carryMaterialResidualJet 2 2*y)*
      (x+carryMaterialResidualJet 2 4/carryMaterialResidualJet 2 2*y) =
      carryMaterialResidualJet 2 2*(x+carryMaterialResidualJet 2 4/carryMaterialResidualJet 2 2*y)^2 := by ring
  rw [he]
  by_cases hy : y = 0
  · subst y
    have hx : x ≠ 0 := hxy.resolve_right (by simp)
    simpa only [mul_zero,add_zero] using mul_pos material_mixed_first_pivot_pos (sq_pos_of_ne_zero hx)
  · have hp : 0 < carryMaterialMixedPivot*y*y := by
      nlinarith [mul_pos material_mixed_pivot_pos (sq_pos_of_ne_zero hy)]
    exact add_pos_of_nonneg_of_pos (mul_nonneg material_mixed_first_pivot_pos.le (sq_nonneg _)) hp

/-- Row germs are recovered from the regular quotient of the FULL valve
balance. The excluded noncentral diagonal is not identified as a kernel. -/
theorem material_valve_confluent_row_germ (eta : ℝ) (heta : eta ≠ 0) :
    ∀ᶠ u : ℝ in nhds 0,
      (fun t => carryValveConfluentReadout eta t u) =ᶠ[nhds 0]
        fun t => (carryMaterialRealResidual t u : ℂ) := by
  obtain ⟨U,hU,h0,hR⟩ := material_valve_global_residual_numerator eta heta
  have hF0 : baseTwoCanonicalResponse 0 ≠ 0 := by
    rw [baseTwoCanonicalResponse_eq_dressing_mul_signal]
    exact mul_ne_zero (baseTwoCanonicalDressingScalar_ne_zero 0) carryMaterial_origin_signal_ne_zero
  have hF := (baseTwoCanonicalResponse_analyticAt 0).continuousAt.eventually_ne hF0
  filter_upwards [hU.mem_nhds h0,hF] with u hu hFu
  by_cases huz : u = 0
  · subst u
    filter_upwards [] with t
    simp only [carryValveConfluentReadout_zero_right,material_real_residual_zero_right,Complex.ofReal_zero]
  · have htu : ∀ᶠ t : ℝ in nhds 0, u ≠ t :=
      (isOpen_ne_fun continuous_const continuous_id).mem_nhds huz
    filter_upwards [hU.mem_nhds h0,hF,htu] with t ht hFt hne
    by_cases htz : t = 0
    · subst t
      simp only [carryValveConfluentReadout_zero_left,material_real_residual_zero_left,Complex.ofReal_zero]
    · have hreg := carryValveResidualFactor_ne_zero t u material_scale_pos.ne' htz huz hne hFt hFu
      rw [carryValveConfluentReadout,if_neg hreg,hR t ht u hu]
      change carryValveResidualFactor t u*(carryMaterialRealResidual t u : ℂ)/
        carryValveResidualFactor t u = _
      exact mul_div_cancel_left₀ _ hreg

theorem material_valve_confluent_jet (eta : ℝ) (heta : eta ≠ 0) (p q : ℕ) :
    carryValveConfluentJet eta p q =
      carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) p q :=
  carryKernelJet_germ (material_valve_confluent_row_germ eta heta) p q

theorem material_valve_mixed_block (eta : ℝ) (heta : eta ≠ 0) (x y v w : ℝ) :
    carryValveMixedBlock eta x y v w = carryMaterialMixedBlock x y v w := by
  simp only [carryValveMixedBlock,material_valve_confluent_jet eta heta,
    carryMaterialMixedBlock,carryMaterialResidualJet]

theorem material_valve_mixed_critical (eta : ℝ) (heta : eta ≠ 0) :
    carryValveMixedBlock eta
      (-carryMaterialResidualJet 4 2/carryMaterialResidualJet 2 2) 1
      (-carryMaterialResidualJet 2 4/carryMaterialResidualJet 2 2) 1 =
        sourceMomentSchur h 0 2 := by
  rw [material_valve_mixed_block eta heta,
    carryMaterialMixedBlock_critical material_mixed_first_pivot_pos.ne',material_mixed_pivot_eq_schur]

/-- Only this finite confluent block is signed, with no assertion about all
finite time samples or higher Schur pivots. -/
theorem material_valve_mixed_block_pos (eta : ℝ) (heta : eta ≠ 0)
    (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < carryValveMixedBlock eta x y x y := by
  rw [material_valve_mixed_block eta heta]
  exact material_mixed_block_pos x y hxy

-- Independent ordered jet orders, not diagonal-only or vertical indices.
example : (carryValveConfluentJet 1 2 4).re = h 3-h 1*h 2/h 0 := by
  rw [material_valve_confluent_jet 1 (by norm_num)]
  exact material_mixed_entries.2.1

-- The imaginary quadrature is checked after the complete complex readout.
example : (carryValveConfluentJet 1 2 4).im = 0 := by
  rw [material_valve_confluent_jet 1 (by norm_num)]
  have he := material_residual_complex_jet_even_even 1 2
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at he
  rw [he]
  rfl

example : carryMaterialResidualJet 1 3 = h 2 := material_residual_jet_odd_odd 0 1
example : carryMaterialResidualJet 2 3 = 0 := material_residual_jet_even_odd 1 1

-- The regular quotient representative deliberately does not claim a full
-- kernel equality on the noncentral diagonal.
example (eta t : ℝ) : carryValveConfluentReadout eta t t = 0 := by
  simp [carryValveConfluentReadout,carryValveResidualFactor]

example : 0 < carryValveMixedBlock 1
    (-carryMaterialResidualJet 4 2/carryMaterialResidualJet 2 2) 1
    (-carryMaterialResidualJet 2 4/carryMaterialResidualJet 2 2) 1 :=
  by
    rw [material_valve_mixed_critical 1 (by norm_num),← material_mixed_pivot_eq_schur]
    exact material_mixed_pivot_pos


end
end CarryMaterialMixedSchurComparison

namespace CarryMaterialMixedSchurComparison
#assert_central_comparison_axioms material_response_real_analytic
#print axioms material_response_real_analytic
#assert_central_comparison_axioms material_residual_complex_jet_source
#print axioms material_residual_complex_jet_source
#assert_central_comparison_axioms material_residual_jet_source
#print axioms material_residual_jet_source
#assert_central_comparison_axioms material_residual_complex_jet_even_even
#print axioms material_residual_complex_jet_even_even
#assert_central_comparison_axioms material_residual_jet_even_even
#print axioms material_residual_jet_even_even
#assert_central_comparison_axioms material_residual_jet_odd_odd
#print axioms material_residual_jet_odd_odd
#assert_central_comparison_axioms material_residual_jet_even_odd
#print axioms material_residual_jet_even_odd
#assert_central_comparison_axioms material_residual_jet_odd_even
#print axioms material_residual_jet_odd_even
#assert_central_comparison_axioms material_mixed_entries
#print axioms material_mixed_entries
#assert_central_comparison_axioms material_mixed_first_pivot_pos
#print axioms material_mixed_first_pivot_pos
#assert_central_comparison_axioms material_mixed_pivot_eq
#print axioms material_mixed_pivot_eq
#assert_central_comparison_axioms material_third_schur_eq
#print axioms material_third_schur_eq
#assert_central_comparison_axioms material_mixed_pivot_eq_schur
#print axioms material_mixed_pivot_eq_schur
#assert_central_comparison_axioms material_mixed_pivot_theta
#print axioms material_mixed_pivot_theta
#assert_central_comparison_axioms material_third_schur_ratio
#print axioms material_third_schur_ratio
#assert_central_comparison_axioms material_mixed_pivot_pos
#print axioms material_mixed_pivot_pos
#assert_central_comparison_axioms material_mixed_cross_dominance
#print axioms material_mixed_cross_dominance
#assert_central_comparison_axioms material_mixed_block_pos
#print axioms material_mixed_block_pos
#assert_central_comparison_axioms material_valve_confluent_row_germ
#print axioms material_valve_confluent_row_germ
#assert_central_comparison_axioms material_valve_confluent_jet
#print axioms material_valve_confluent_jet
#assert_central_comparison_axioms material_valve_mixed_block
#print axioms material_valve_mixed_block
#assert_central_comparison_axioms material_valve_mixed_critical
#print axioms material_valve_mixed_critical
#assert_central_comparison_axioms material_valve_mixed_block_pos
#print axioms material_valve_mixed_block_pos
end CarryMaterialMixedSchurComparison


namespace CarryMaterialSourceFactorComparison
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open CarrySelfAdjointOperator.SourcePositiveReduction
open CarryMaterialMixedSchurComparison
open scoped Matrix
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
local notation "h" => canonicalCompletedNativeLogDerivativeMoment

theorem material_even_pairing_source (i j : ℕ) :
    carryMaterialEvenPairing i j = h (i+j+2)-h (i+1)*h (j+1)/h 0 := by
  have he : i+1+(j+1) = i+j+2 := by omega
  simpa only [carryMaterialEvenPairing,he] using material_residual_jet_even_even (i+1) (j+1)

theorem material_even_pairing_symm (i j : ℕ) :
    carryMaterialEvenPairing i j = carryMaterialEvenPairing j i := by
  rw [material_even_pairing_source,material_even_pairing_source]
  rw [Nat.add_comm j i]
  ring

theorem material_odd_pairing_source (i j : ℕ) :
    carryMaterialOddPairing i j = h (i+j+1) := by
  exact material_residual_jet_odd_odd i j

theorem material_even_pivot_zero_pos : 0 < carryPairingPivot carryMaterialEvenPairing 0 :=
  material_mixed_first_pivot_pos

theorem material_even_pivot_one_eq :
    carryPairingPivot carryMaterialEvenPairing 1 = carryMaterialMixedPivot := rfl

theorem material_even_pivot_one_pos : 0 < carryPairingPivot carryMaterialEvenPairing 1 := by
  rw [material_even_pivot_one_eq]
  exact material_mixed_pivot_pos

/-- New physical order-six pivot, computed by the source's ordered
elimination, not defined by a determinant certificate. -/
theorem material_even_pivot_two_ratio :
    carryPairingPivot carryMaterialEvenPairing 2 =
      nativeSourceSevenEvenDiscriminant/(2*nativeSourceFiveEvenDiscriminant) := by
  rw [carryPairingPivot_two]
  simp_rw [material_even_pairing_source]
  norm_num only [Nat.reduceAdd]
  have h0 : h 0 ≠ 0 := canonicalCompletedNativeLogDerivativeMoment_zero_pos.ne'
  have hA : h 2-h 1*h 1/h 0 = (h 0*h 2-h 1^2)/h 0 := by
    field_simp [h0]
  have hP : h 4-h 2*h 2/h 0-(h 3-h 2*h 1/h 0)*(h 3-h 1*h 2/h 0)/
      (h 2-h 1*h 1/h 0) =
        nativeSourceFiveEvenDiscriminant/(8*(h 0*h 2-h 1^2)) := by
    simpa only [pow_two,mul_comm (h 2) (h 1)] using
      material_third_schur_eq.symm.trans material_third_schur_ratio
  rw [hP,hA]
  have hd := nativeMoment_first_discriminant_pos.ne'
  have hD := nativeSourceFiveEvenDiscriminant_pos.ne'
  field_simp [h0,hd,hD]
  unfold nativeSourceSevenEvenDiscriminant nativeSourceSevenEvenCoupling0
    nativeSourceSevenEvenCoupling1 nativeSourceSevenEvenCoupling2
    nativeSourceFiveEvenDiscriminant
  simp_rw [nativeSourceOddBoundaryCoefficient_eq_twice_primeDepthGeometricMoment,
    primeDepthGeometricMoment_eq_canonical]
  ring

/-- Strict sign transported from the existing raw theta certificate. This
does not supply a new sign certificate at an unproved source order. -/
theorem material_even_pivot_two_pos : 0 < carryPairingPivot carryMaterialEvenPairing 2 := by
  rw [material_even_pivot_two_ratio]
  exact div_pos nativeSourceSevenEvenDiscriminant_pos
    (mul_pos (by norm_num) nativeSourceFiveEvenDiscriminant_pos)

theorem material_even_pivots_three_pos (r : ℕ) (hr : r < 3) :
    0 < carryPairingPivot carryMaterialEvenPairing r := by
  interval_cases r
  · exact material_even_pivot_zero_pos
  · exact material_even_pivot_one_pos
  · exact material_even_pivot_two_pos

/-- An actual real factor of the physical residual block at Taylor orders
2, 4, 6, with no `PosDef` input. All nine crossings are retained. -/
theorem material_even_cholesky_three :
    carryMaterialEvenCholesky 3 * (carryMaterialEvenCholesky 3)ᵀ =
      (fun i j : Fin 3 => carryMaterialResidualJet (2*(i.val+1)) (2*(j.val+1))) :=
  carryPairingCholesky_identity material_even_pairing_symm 3 material_even_pivots_three_pos

theorem material_even_cholesky_three_det_pos :
    0 < (carryMaterialEvenCholesky 3).det :=
  carryPairingCholesky_det_pos carryMaterialEvenPairing 3 material_even_pivots_three_pos

/-- Two independent coefficient vectors; this is stronger than a diagonal
energy formula and retains every original ordered mixed term. -/
theorem material_even_bilinear_three (x y : Fin 3 → ℝ) :
    carryPairingBilinear carryMaterialEvenPairing 3 x y =
      ∑ r : Fin 3, carryPairingPivot carryMaterialEvenPairing r *
        (∑ i : Fin 3, carryPairingColumn carryMaterialEvenPairing r i*x i) *
        (∑ j : Fin 3, carryPairingColumn carryMaterialEvenPairing r j*y j) :=
  carryPairingBilinear_factor material_even_pairing_symm 3
    (fun r hr => (material_even_pivots_three_pos r hr).ne') x y

/-- A derived Cholesky factor for the original unshifted four-by-four native
Hankel section, restoring the central channel with its literal normalization. -/
def material_hankel_cholesky_four : Matrix (Fin 4) (Fin 4) ℝ :=
  carryPairingBorderFactor (h 0) (fun i : Fin 3 => h (i.val+1)) (carryMaterialEvenCholesky 3)

theorem material_hankel_cholesky_four_identity :
    material_hankel_cholesky_four*material_hankel_cholesky_fourᵀ =
      (fun i j : Fin 4 => h (i.val+j.val)) := by
  have ha := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · refine Fin.cases ?_ (fun r => ?_) j
    · exact carryPairingBorderFactor_origin (h 0) ha.le _ _
    · simpa only [material_hankel_cholesky_four,Fin.val_zero,Fin.val_succ,Nat.zero_add] using
        carryPairingBorderFactor_origin_succ (h 0) ha (fun i : Fin 3 => h (i.val+1))
          (carryMaterialEvenCholesky 3) r
  · refine Fin.cases ?_ (fun r => ?_) j
    · exact carryPairingBorderFactor_succ_origin (h 0) ha _ _ k
    · change (carryPairingBorderFactor (h 0) (fun i : Fin 3 => h (i.val+1))
        (carryMaterialEvenCholesky 3)*
        (carryPairingBorderFactor (h 0) (fun i : Fin 3 => h (i.val+1))
          (carryMaterialEvenCholesky 3))ᵀ) k.succ r.succ = _
      rw [carryPairingBorderFactor_succ_succ (h 0) ha,material_even_cholesky_three]
      change h (k.val+1)*h (r.val+1)/h 0+carryMaterialEvenPairing k r = _
      rw [material_even_pairing_source]
      have he : k.val+1+(r.val+1) = k.val+r.val+2 := by omega
      change _ = h (k.val+1+(r.val+1))
      rw [he]
      ring

theorem material_hankel_cholesky_four_det_pos : 0 < material_hankel_cholesky_four.det := by
  apply carryPairingBorderFactor_det_pos (h 0) canonicalCompletedNativeLogDerivativeMoment_zero_pos
  · intro i j hij
    exact carryPairingCholesky_above carryMaterialEvenPairing 3
      (fun r hr => (material_even_pivots_three_pos r hr).ne') i j hij
  · intro i
    rw [carryMaterialEvenCholesky,carryPairingCholesky_diagonal carryMaterialEvenPairing 3
      (fun r hr => (material_even_pivots_three_pos r hr).ne')]
    exact Real.sqrt_pos.mpr (material_even_pivots_three_pos i i.isLt)

/-- Universal algebraic expansion on the actual source observations. No
sign, nonzero-pivot or all-order positivity assumption is needed here. -/
theorem material_even_signed_prefix (n i j : ℕ) :
    carryMaterialResidualJet (2*(i+1)) (2*(j+1)) =
      (∑ r ∈ Finset.range n, carryPairingPivot carryMaterialEvenPairing r *
        carryPairingColumn carryMaterialEvenPairing r i *
        carryPairingColumn carryMaterialEvenPairing r j) +
          carryPairingRemainder carryMaterialEvenPairing n i j :=
  carryPairing_signed_prefix material_even_pairing_symm n i j

theorem material_even_real_factor_defect (n : ℕ) (i j : Fin n) :
    carryMaterialResidualJet (2*(i.val+1)) (2*(j.val+1)) =
      (carryMaterialEvenCholesky n*(carryMaterialEvenCholesky n)ᵀ) i j+
        carryPairingRemainder carryMaterialEvenPairing n i j-
        ∑ r : Fin n, max (-carryPairingPivot carryMaterialEvenPairing r) 0 *
          carryPairingColumn carryMaterialEvenPairing r i *
          carryPairingColumn carryMaterialEvenPairing r j :=
  carryPairingCholesky_defect material_even_pairing_symm n i j

theorem material_even_three_posDef :
    Matrix.PosDef (fun i j : Fin 3 => carryMaterialEvenPairing i j) :=
  carryPairingCholesky_posDef material_even_pairing_symm 3 material_even_pivots_three_pos

theorem material_even_energy_three_pos (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    0 < carryPairingBilinear carryMaterialEvenPairing 3 x x := by
  rw [carryPairingBilinear_eq_dotProduct]
  exact material_even_three_posDef.dotProduct_mulVec_pos hx

/-- Full complex confluent observations are reconstructed: their imaginary
quadrature vanishes by the original source identity, not by a projection. -/
theorem material_complex_even_factor_three (i j : Fin 3) :
    carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ))
      (2*(i.val+1)) (2*(j.val+1)) =
      (((carryMaterialEvenCholesky 3*(carryMaterialEvenCholesky 3)ᵀ) i j : ℝ) : ℂ) := by
  rw [material_even_cholesky_three]
  have he := material_residual_complex_jet_even_even (i.val+1) (j.val+1)
  change carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ))
    (2*(i.val+1)) (2*(j.val+1)) =
      (carryMaterialResidualJet (2*(i.val+1)) (2*(j.val+1)) : ℂ)
  rw [material_residual_jet_even_even]
  exact he

theorem material_valve_even_factor_three (eta : ℝ) (heta : eta ≠ 0) (i j : Fin 3) :
    carryValveConfluentJet eta (2*(i.val+1)) (2*(j.val+1)) =
      (((carryMaterialEvenCholesky 3*(carryMaterialEvenCholesky 3)ᵀ) i j : ℝ) : ℂ) := by
  rw [material_valve_confluent_jet eta heta]
  exact material_complex_even_factor_three i j

end
end CarryMaterialSourceFactorComparison

namespace CarryMaterialSourceFactorComparison
#assert_central_comparison_axioms material_even_pairing_source
#print axioms material_even_pairing_source
#assert_central_comparison_axioms material_even_pairing_symm
#print axioms material_even_pairing_symm
#assert_central_comparison_axioms material_odd_pairing_source
#print axioms material_odd_pairing_source
#assert_central_comparison_axioms material_even_pivot_zero_pos
#print axioms material_even_pivot_zero_pos
#assert_central_comparison_axioms material_even_pivot_one_eq
#print axioms material_even_pivot_one_eq
#assert_central_comparison_axioms material_even_pivot_one_pos
#print axioms material_even_pivot_one_pos
#assert_central_comparison_axioms material_even_pivot_two_ratio
#print axioms material_even_pivot_two_ratio
#assert_central_comparison_axioms material_even_pivot_two_pos
#print axioms material_even_pivot_two_pos
#assert_central_comparison_axioms material_even_pivots_three_pos
#print axioms material_even_pivots_three_pos
#assert_central_comparison_axioms material_even_cholesky_three
#print axioms material_even_cholesky_three
#assert_central_comparison_axioms material_even_cholesky_three_det_pos
#print axioms material_even_cholesky_three_det_pos
#assert_central_comparison_axioms material_even_bilinear_three
#print axioms material_even_bilinear_three
#assert_central_comparison_axioms material_hankel_cholesky_four
#print axioms material_hankel_cholesky_four
#assert_central_comparison_axioms material_hankel_cholesky_four_identity
#print axioms material_hankel_cholesky_four_identity
#assert_central_comparison_axioms material_hankel_cholesky_four_det_pos
#print axioms material_hankel_cholesky_four_det_pos
#assert_central_comparison_axioms material_even_signed_prefix
#print axioms material_even_signed_prefix
#assert_central_comparison_axioms material_even_real_factor_defect
#print axioms material_even_real_factor_defect
#assert_central_comparison_axioms material_even_three_posDef
#print axioms material_even_three_posDef
#assert_central_comparison_axioms material_even_energy_three_pos
#print axioms material_even_energy_three_pos
#assert_central_comparison_axioms material_complex_even_factor_three
#print axioms material_complex_even_factor_three
#assert_central_comparison_axioms material_valve_even_factor_three
#print axioms material_valve_even_factor_three
end CarryMaterialSourceFactorComparison


namespace CarryMaterialFourthPivotComparison
open GeometryOfNumbers.Analysis CarrySelfAdjointOperator
open CarrySelfAdjointOperator.SourcePositiveReduction
open CarryMaterialSourceFactorComparison CarryMaterialMixedSchurComparison
open CarryMaterialNullHierarchyComparison CarryMaterialResponseComparison
open CarryMaterialThirdNullComparison
open MeasureTheory
open scoped Matrix ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
local notation "h" => canonicalCompletedNativeLogDerivativeMoment
local notation "c" => completedNativeRealEvenCharacteristicCoefficient

theorem material_fourth_threshold_eq :
    carryMaterialFourthSourceThreshold = h 4^2/h 0+carryMaterialFourthOldCoupling := by
  have he : (carryMaterialTaylorShift 9 0).re = h 4 := by
    rw [material_taylor_shift_center,
      show 9=2*4+1 by norm_num,completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
    rfl
  rw [carryMaterialFourthSourceThreshold,he,material_scale_eq]

/-- The only new moment is h8. The threshold retains all old-new crossings
and the previously extracted central channel with its original normalization. -/
theorem material_fourth_pivot_source :
    carryMaterialFourthPivot = h 8-carryMaterialFourthSourceThreshold := by
  rw [carryMaterialFourthPivot_split,material_fourth_threshold_eq]
  have he := material_residual_jet_even_even 4 4
  norm_num only [Nat.reduceMul,Nat.reduceAdd] at he
  rw [he]
  ring

theorem material_fourth_old_coupling_squares : carryMaterialFourthOldCoupling =
    (carryMaterialEvenPairing 0 3)^2/carryPairingPivot carryMaterialEvenPairing 0+
      (carryPairingRemainder carryMaterialEvenPairing 1 1 3)^2/
        carryPairingPivot carryMaterialEvenPairing 1+
      (carryPairingRemainder carryMaterialEvenPairing 2 2 3)^2/
        carryPairingPivot carryMaterialEvenPairing 2 := by
  unfold carryMaterialFourthOldCoupling
  rw [material_even_pairing_symm 3 0,
    carryPairingRemainder_symm material_even_pairing_symm 1 3 1,
    carryPairingRemainder_symm material_even_pairing_symm 2 3 2]
  ring

theorem material_fourth_old_coupling_nonneg : 0 ≤ carryMaterialFourthOldCoupling := by
  rw [material_fourth_old_coupling_squares]
  exact add_nonneg (add_nonneg
    (div_nonneg (sq_nonneg _) material_even_pivot_zero_pos.le)
    (div_nonneg (sq_nonneg _) material_even_pivot_one_pos.le))
    (div_nonneg (sq_nonneg _) material_even_pivot_two_pos.le)

/-- Literal recurrence of the unchanged completed characteristic. There is
no guessed fourth source sign and no adjusted normalization. -/
theorem material_fourth_pivot_characteristic :
    c 0*carryMaterialFourthPivot = -9*c 9-
      (∑ k ∈ Finset.range 8, h k*c (8-k))-c 0*carryMaterialFourthSourceThreshold := by
  have he := canonicalCompletedNativeLogDerivativeMoment_real_recurrence 8
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at he
  rw [material_fourth_pivot_source]
  nlinarith only [he]

/-- All terms on the right precede c9: h0,...,h7, c0,...,c8 and the actual
source couplings. This is an exact remaining gate, not an input certificate. -/
def material_fourth_characteristic_ceiling : ℝ :=
  -((∑ k ∈ Finset.range 8, h k*c (8-k))+c 0*carryMaterialFourthSourceThreshold)/9

theorem material_fourth_pivot_pos_iff_characteristic :
    0 < carryMaterialFourthPivot ↔ c 9 < material_fourth_characteristic_ceiling := by
  have he := material_fourth_pivot_characteristic
  have hc : 0 < c 0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/3)
    completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  unfold material_fourth_characteristic_ceiling
  constructor <;> intro hp <;> nlinarith

/-- The coefficient needed for this pivot uses genuine theta-tail moments
16 and 18. It is distinct from the eighth-source odd-sector coefficient c8. -/
theorem material_fourth_c9_theta :
    c 9 = (completedNativeThetaTailMoment 18-1224*completedNativeThetaTailMoment 16)/
      (4*(Nat.factorial 18 : ℝ)) := by
  rw [completedNativeRealEvenCharacteristicCoefficient_eq_cosineMoment_allOrder]
  have he := completedNativeXiCosineMoment_succ_eq_thetaTailMoments 8
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at he
  norm_num only [Nat.reduceMul,show (-1 : ℝ)^9 = -1 by norm_num]
  rw [show completedNativeXiCosineMoment 9 =
      306*completedNativeThetaTailMoment 16-(1/4:ℝ)*completedNativeThetaTailMoment 18 by exact he]
  norm_num [Nat.factorial]
  ring

theorem material_fourth_pivot_pos_iff_theta_balance :
    0 < carryMaterialFourthPivot ↔
      1224*completedNativeThetaTailMoment 16-completedNativeThetaTailMoment 18 >
        -4*(Nat.factorial 18 : ℝ)*material_fourth_characteristic_ceiling := by
  rw [material_fourth_pivot_pos_iff_characteristic,material_fourth_c9_theta]
  norm_num [Nat.factorial]
  constructor <;> intro hp <;> linarith

/-- The original complete theta integral, without dropping its signed tail
or exchanging an unproved Green/trace decomposition with an infinite sum. -/
theorem material_fourth_theta_balance_integral :
    (∫ u in Set.Ioi (0 : ℝ), (1224*u^16-u^18)*XiThetaCosine.thetaTail u) =
      1224*completedNativeThetaTailMoment 16-completedNativeThetaTailMoment 18 := by
  have h16 := (integrableOn_pow_mul_thetaTail 16).const_mul (1224 : ℝ)
  have h18 := integrableOn_pow_mul_thetaTail 18
  have he : (fun u : ℝ => (1224*u^16-u^18)*XiThetaCosine.thetaTail u) =
      fun u => 1224*(u^16*XiThetaCosine.thetaTail u)-u^18*XiThetaCosine.thetaTail u := by
    funext u
    ring
  rw [he,MeasureTheory.integral_sub h16 h18,MeasureTheory.integral_const_mul]
  rfl

theorem material_fourth_pivot_pos_iff_theta_integral :
    0 < carryMaterialFourthPivot ↔
      (∫ u in Set.Ioi (0 : ℝ), (1224*u^16-u^18)*XiThetaCosine.thetaTail u) >
        -4*(Nat.factorial 18 : ℝ)*material_fourth_characteristic_ceiling := by
  rw [material_fourth_theta_balance_integral]
  exact material_fourth_pivot_pos_iff_theta_balance

/-- Four-channel polarized sewing with the three old source signs discharged.
The new source pivot remains explicitly signed. -/
theorem material_fourth_bilinear (x y : Fin 4 → ℝ) :
    carryPairingBilinear carryMaterialEvenPairing 4 x y =
      (∑ r : Fin 3, carryPairingPivot carryMaterialEvenPairing r *
        (∑ i : Fin 4, carryPairingColumn carryMaterialEvenPairing r i*x i) *
        (∑ j : Fin 4, carryPairingColumn carryMaterialEvenPairing r j*y j))+
          carryMaterialFourthPivot*x 3*y 3 :=
  carryMaterialFourthBilinear_sewing material_even_pairing_symm
    (fun r hr => (material_even_pivots_three_pos r hr).ne') x y

/-- This nonzero combination cancels precisely the three old columns and
reads the new signed pivot, with no positivity assumption on that pivot. -/
theorem material_fourth_critical_pairing (y : Fin 4 → ℝ) :
    carryPairingBilinear carryMaterialEvenPairing 4 carryMaterialFourthCritical y =
      carryMaterialFourthPivot*y 3 :=
  carryMaterialFourthCritical_pairing material_even_pairing_symm
    (fun r hr => (material_even_pivots_three_pos r hr).ne') y

theorem material_fourth_critical_energy :
    carryPairingBilinear carryMaterialEvenPairing 4
      carryMaterialFourthCritical carryMaterialFourthCritical = carryMaterialFourthPivot := by
  rw [material_fourth_critical_pairing,carryMaterialFourthCritical_last,mul_one]

theorem material_fourth_block_posDef_iff :
    Matrix.PosDef (fun i j : Fin 4 => carryMaterialEvenPairing i j) ↔
      0 < carryMaterialFourthPivot := by
  constructor
  · intro hp
    have he := hp.dotProduct_mulVec_pos carryMaterialFourthCritical_ne_zero
    simp only [star_trivial] at he
    rw [← carryPairingBilinear_eq_dotProduct,material_fourth_critical_energy] at he
    exact he
  · intro hp
    apply carryPairingCholesky_posDef material_even_pairing_symm
    intro r hr
    by_cases hlt : r < 3
    · exact material_even_pivots_three_pos r hlt
    · have he : r = 3 := by omega
      subst r
      exact hp

theorem material_fourth_block_posDef_iff_theta_balance :
    Matrix.PosDef (fun i j : Fin 4 => carryMaterialEvenPairing i j) ↔
      1224*completedNativeThetaTailMoment 16-completedNativeThetaTailMoment 18 >
        -4*(Nat.factorial 18 : ℝ)*material_fourth_characteristic_ceiling := by
  rw [material_fourth_block_posDef_iff,material_fourth_pivot_pos_iff_theta_balance]

/-- Conditional consequence only: the missing source estimate would close
the four-by-four residual block. No proof of the estimate is supplied here. -/
theorem material_fourth_cholesky_of_source_estimate
    (hsource : c 9 < material_fourth_characteristic_ceiling) :
    carryMaterialEvenCholesky 4*(carryMaterialEvenCholesky 4)ᵀ =
      (fun i j : Fin 4 => carryMaterialEvenPairing i j) := by
  apply carryPairingCholesky_identity material_even_pairing_symm
  intro r hr
  by_cases hlt : r < 3
  · exact material_even_pivots_three_pos r hlt
  · have he : r = 3 := by omega
    subst r
    exact material_fourth_pivot_pos_iff_characteristic.mpr hsource

end
end CarryMaterialFourthPivotComparison

namespace CarryMaterialFourthPivotComparison
#assert_central_comparison_axioms material_fourth_threshold_eq
#print axioms material_fourth_threshold_eq
#assert_central_comparison_axioms material_fourth_pivot_source
#print axioms material_fourth_pivot_source
#assert_central_comparison_axioms material_fourth_old_coupling_squares
#print axioms material_fourth_old_coupling_squares
#assert_central_comparison_axioms material_fourth_old_coupling_nonneg
#print axioms material_fourth_old_coupling_nonneg
#assert_central_comparison_axioms material_fourth_pivot_characteristic
#print axioms material_fourth_pivot_characteristic
#assert_central_comparison_axioms material_fourth_characteristic_ceiling
#print axioms material_fourth_characteristic_ceiling
#assert_central_comparison_axioms material_fourth_pivot_pos_iff_characteristic
#print axioms material_fourth_pivot_pos_iff_characteristic
#assert_central_comparison_axioms material_fourth_c9_theta
#print axioms material_fourth_c9_theta
#assert_central_comparison_axioms material_fourth_pivot_pos_iff_theta_balance
#print axioms material_fourth_pivot_pos_iff_theta_balance
#assert_central_comparison_axioms material_fourth_theta_balance_integral
#print axioms material_fourth_theta_balance_integral
#assert_central_comparison_axioms material_fourth_pivot_pos_iff_theta_integral
#print axioms material_fourth_pivot_pos_iff_theta_integral
#assert_central_comparison_axioms material_fourth_bilinear
#print axioms material_fourth_bilinear
#assert_central_comparison_axioms material_fourth_critical_pairing
#print axioms material_fourth_critical_pairing
#assert_central_comparison_axioms material_fourth_critical_energy
#print axioms material_fourth_critical_energy
#assert_central_comparison_axioms material_fourth_block_posDef_iff
#print axioms material_fourth_block_posDef_iff
#assert_central_comparison_axioms material_fourth_block_posDef_iff_theta_balance
#print axioms material_fourth_block_posDef_iff_theta_balance
#assert_central_comparison_axioms material_fourth_cholesky_of_source_estimate
#print axioms material_fourth_cholesky_of_source_estimate
end CarryMaterialFourthPivotComparison
