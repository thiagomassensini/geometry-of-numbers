import GeometryOfNumbers.Analysis.CarryMaterialTfvdGreenReadout

/-! The original completed source, its original norm and bounded readout.
No new source, kernel, metric or normalization is defined. The displayed
sqrt(2) is the fixed Green normalization being tested. -/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false

theorem carryMaterial_source_seed (t : ℝ) :
    (baseTwoCompletedBoundaryHilbertState t).fst = 1 := by
  simp [criticalMaterialSample]

theorem carryMaterialCarrier_norm_sq (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    ‖y‖ ^ 2 = ‖y.fst‖ ^ 2 + ‖y.snd.fst‖ ^ 2 + ‖y.snd.snd‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  ring

theorem carryMaterial_source_norm_sq (t : ℝ) :
    ‖baseTwoCompletedBoundaryHilbertState t‖ ^ 2 =
      1 + ‖baseTwoCompletedMaterialGradientL2 t‖ ^ 2 + ‖baseTwoCompletedBoundaryValue t‖ ^ 2 := by
  rw [carryMaterialCarrier_norm_sq, carryMaterial_source_seed]
  simp only [norm_one, one_pow, baseTwoCompletedBoundaryHilbertState_interior,
    baseTwoCompletedBoundaryHilbertState_boundary]

/-- All four source contributions are retained at the actual parameter zero. -/
theorem carryMaterial_origin_norm_physical_residual :
    ‖baseTwoCompletedBoundaryHilbertState 0‖ ^ 2 =
      1 + ‖baseTwoPhysicalOrdinaryC2State 0‖ ^ 2 +
        ‖baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 0)‖ ^ 2 +
        ‖baseTwoCompletedBoundaryValue 0‖ ^ 2 := by
  rw [carryMaterial_source_norm_sq, baseTwoPhysicalC2Residual_norm_sq]
  simp only [baseTwoPhysicalOrdinaryC2State]
  ring

theorem carryMaterial_origin_boundary :
    baseTwoCompletedBoundaryValue 0 = baseTwoCriticalCompleteSignal 0 - 1 ∧
      (baseTwoCompletedBoundaryValue 0).im = 0 := by
  have h := baseTwoCompletedBoundaryValue_add_seed_eq_signal 0
  have hs : criticalMaterialSample 0 1 = 1 := by simp [criticalMaterialSample]
  rw [hs] at h
  constructor
  · linear_combination h
  · have hi := congrArg Complex.im h
    simpa [baseTwoCriticalCompleteSignal_zero_im] using hi

theorem carryMaterial_origin_signal_ne_zero : baseTwoCriticalCompleteSignal 0 ≠ 0 := by
  intro h
  have hp := baseTwoCriticalCompleteSignal_zero_re_pos
  rw [h] at hp
  norm_num at hp

theorem carryMaterial_origin_gradient_norm_pos : 0 < ‖baseTwoCompletedMaterialGradientL2 0‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have h := congrArg (fun g : MaterialEdgeL2 => (g 0).re) hz
  simp only [baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply] at h
  norm_num [criticalMaterialGradient, criticalMaterialSample] at h
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

/-- Parallelogram identity for the EXISTING seed+return readout. The gradient
and seed-return imbalance are the exact excess, rather than omitted norms. -/
theorem carryMaterial_readout_norm_gap (y : BaseTwoCompletedBoundaryHilbertCarrier) :
    2 * ‖y‖ ^ 2 - ‖baseTwoCompletedBoundaryHilbertReadout y‖ ^ 2 =
      2 * ‖y.snd.fst‖ ^ 2 + ‖y.fst - y.snd.snd‖ ^ 2 := by
  have hp := parallelogram_law_with_norm ℂ y.fst y.snd.snd
  rw [carryMaterialCarrier_norm_sq, baseTwoCompletedBoundaryHilbertReadout_apply]
  linarith

theorem carryMaterial_origin_readout_norm_gap :
    2 * ‖baseTwoCompletedBoundaryHilbertState 0‖ ^ 2 - ‖baseTwoCriticalCompleteSignal 0‖ ^ 2 =
      2 * ‖baseTwoCompletedMaterialGradientL2 0‖ ^ 2 + ‖1 - baseTwoCompletedBoundaryValue 0‖ ^ 2 := by
  simpa only [baseTwoCompletedBoundaryHilbertReadout_eq_signal, carryMaterial_source_seed,
    baseTwoCompletedBoundaryHilbertState_interior, baseTwoCompletedBoundaryHilbertState_boundary] using
    carryMaterial_readout_norm_gap (baseTwoCompletedBoundaryHilbertState 0)

/-- Cancellation of the original dressing, after exact scalar synthesis.
This is an algebraic equality of the literal candidate, not a fitted factor. -/
theorem carryMaterial_origin_dressing_cancel :
    (((Real.sqrt 2 : ℝ) : ℂ) * baseTwoCanonicalResponse 0)⁻¹ •
        baseTwoVectorDressing 0 (baseTwoCompletedBoundaryHilbertState 0) =
      (((Real.sqrt 2 : ℝ) : ℂ) * baseTwoCriticalCompleteSignal 0)⁻¹ •
        baseTwoCompletedBoundaryHilbertState 0 := by
  rw [baseTwoVectorDressing_apply, smul_smul,
    baseTwoCanonicalResponse_eq_dressing_mul_signal]
  congr 1
  have hd := baseTwoCanonicalDressingScalar_ne_zero 0
  have hs := carryMaterial_origin_signal_ne_zero
  have hr : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  field_simp

theorem carryMaterial_origin_normalized_mass :
    ‖(((Real.sqrt 2 : ℝ) : ℂ) * baseTwoCanonicalResponse 0)⁻¹ •
        baseTwoVectorDressing 0 (baseTwoCompletedBoundaryHilbertState 0)‖ ^ 2 =
      ‖baseTwoCompletedBoundaryHilbertState 0‖ ^ 2 / (2 * ‖baseTwoCriticalCompleteSignal 0‖ ^ 2) := by
  rw [carryMaterial_origin_dressing_cancel]
  have hr : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]
  simp only [norm_smul, norm_inv, norm_mul, mul_pow, inv_pow, hr, div_eq_mul_inv]
  ring

/-- Exact central defect for this one literal source and its own completed
scalar readout. The scalar h can later be instantiated by the actual moment. -/
theorem carryMaterial_origin_normalized_defect (h : ℝ) :
    ‖(((Real.sqrt 2 : ℝ) : ℂ) * baseTwoCanonicalResponse 0)⁻¹ •
        baseTwoVectorDressing 0 (baseTwoCompletedBoundaryHilbertState 0)‖ ^ 2 - h =
      (1 / 4 - h) + (2 * ‖baseTwoCompletedMaterialGradientL2 0‖ ^ 2 +
        ‖1 - baseTwoCompletedBoundaryValue 0‖ ^ 2) / (4 * ‖baseTwoCriticalCompleteSignal 0‖ ^ 2) := by
  rw [carryMaterial_origin_normalized_mass]
  have hs : ‖baseTwoCriticalCompleteSignal 0‖ ≠ 0 := norm_ne_zero_iff.mpr carryMaterial_origin_signal_ne_zero
  have hg := carryMaterial_origin_readout_norm_gap
  field_simp
  nlinarith

theorem carryMaterial_origin_normalized_defect_physical (h : ℝ) :
    ‖(((Real.sqrt 2 : ℝ) : ℂ) * baseTwoCanonicalResponse 0)⁻¹ •
        baseTwoVectorDressing 0 (baseTwoCompletedBoundaryHilbertState 0)‖ ^ 2 - h =
      (1 / 4 - h) + (2 * ‖baseTwoPhysicalOrdinaryC2State 0‖ ^ 2 +
        2 * ‖baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 0)‖ ^ 2 +
        ‖1 - baseTwoCompletedBoundaryValue 0‖ ^ 2) / (4 * ‖baseTwoCriticalCompleteSignal 0‖ ^ 2) := by
  rw [carryMaterial_origin_normalized_defect, baseTwoPhysicalC2Residual_norm_sq]
  simp only [baseTwoPhysicalOrdinaryC2State]
  ring

theorem carryMaterial_origin_normalized_mass_gt_quarter :
    (1 / 4 : ℝ) <
      ‖(((Real.sqrt 2 : ℝ) : ℂ) * baseTwoCanonicalResponse 0)⁻¹ •
        baseTwoVectorDressing 0 (baseTwoCompletedBoundaryHilbertState 0)‖ ^ 2 := by
  have he := carryMaterial_origin_normalized_defect (1 / 4)
  have hg := carryMaterial_origin_gradient_norm_pos
  have hs := norm_pos_iff.mpr carryMaterial_origin_signal_ne_zero
  have hd : 0 < (2 * ‖baseTwoCompletedMaterialGradientL2 0‖ ^ 2 +
      ‖1 - baseTwoCompletedBoundaryValue 0‖ ^ 2) / (4 * ‖baseTwoCriticalCompleteSignal 0‖ ^ 2) := by
    apply div_pos _ (by positivity)
    nlinarith [sq_nonneg ‖1 - baseTwoCompletedBoundaryValue 0‖]
  linarith

end
end GeometryOfNumbers.Analysis
