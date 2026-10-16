import GeometryOfNumbers.Analysis.CarryMaterialCentralCalibration
import CarrySelfAdjointOperator.C2GeometryNativeSourceBridge
import CarrySelfAdjointOperator.CompletedC3KernelMetricCalibration
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
#assert_central_comparison_axioms no_normalized_kernel_with_literal_material_origin
#print axioms no_normalized_kernel_with_literal_material_origin
end CarryMaterialCanonicalComparison
