import GeometryOfNumbers.Analysis.C2GreenTemporalMeanCanary
import GreenFrame.Concrete.Analysis.CanonicalParseval

/-!
# Metric genealogy: geometric C2 isometries, raw Green, canonical Parseval

Normalization begins after the vertical stencil. The upstream real geometry
and all previous sources and analyses remain unchanged.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp InnerProduct InnerProductSpace

namespace GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
open GeometryOfNumbers.Analysis GreenFrame.Concrete
open C2GlobalGreenBridge C2GreenPreStencilCanary C2GreenTemporalMeanCanary

/-- The existing concrete operator, with its fixed canonical partition. -/
abbrev canonicalRawGreenAnalysis : State →L[ℂ] ConcreteAnalysisSpace :=
  concreteAnalysisOperator canonicalCarryInfinitePartition

/-- Reuse the proved frame certificate; no additional bounds are assumed. -/
abbrev canonicalRawGreenFrameBounds : ComplexFrameBounds canonicalRawGreenAnalysis :=
  (concreteSplitFrameBounds canonicalCarryInfinitePartition).toComplexFrameBounds

/-- A concrete core-one state in the real first quadrature. -/
def c2RawMetricWitness : CoreState :=
  lp.single 2 (⟨1, by norm_num, by norm_num⟩ : PositiveOddCore)
    (realPlaneHilbertEquiv (1,0))

theorem c2RawMetricWitness_ne_zero : c2RawMetricWitness ≠ 0 := by
  intro hz
  let m : PositiveOddCore := ⟨1,by norm_num,by norm_num⟩
  have h := congrArg (fun X : CoreState => realPlaneHilbertEquiv.symm (X m)) hz
  simp [c2RawMetricWitness, m] at h

theorem c2RawMetricWitness_norm : ‖c2RawMetricWitness‖ = 1 := by
  unfold c2RawMetricWitness
  rw [lp.norm_single (by norm_num)]
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [← realPlaneHilbert_energy_eq_norm_sq, LinearEquiv.symm_apply_apply]
  norm_num [realPlaneEnergy]

theorem c2RawMetricWitness_exists_time_defect_pos :
    ∃ t : ℝ, 0 < c2GlobalRawGreenDefect t c2RawMetricWitness :=
  exists_time_rawGreenDefect_pos c2RawMetricWitness c2RawMetricWitness_ne_zero

/-- Express the preexisting defect directly in the material input metric. -/
theorem c2RawGreenDefect_eq_material_norm_sq_sub (t : ℝ) (V : CoreState) :
    c2GlobalRawGreenDefect t V =
      ‖canonicalRawGreenAnalysis (c2GlobalGreenInputIsometry t V)‖ ^ 2 -
      ‖c2GlobalGreenInputIsometry t V‖ ^ 2 := by
  rw [c2GlobalRawGreenDefect, c2GlobalGreenAnalysis_apply, c2GlobalGreenInput_norm]

/-- The raw Green norm increase is witnessed inside the original C2 source range. -/
theorem exists_c2_time_rawGreen_norm_sq_gt :
    ∃ t : ℝ, ‖c2GlobalGreenInputIsometry t c2RawMetricWitness‖ ^ 2 <
      ‖canonicalRawGreenAnalysis (c2GlobalGreenInputIsometry t c2RawMetricWitness)‖ ^ 2 := by
  obtain ⟨t,ht⟩ := c2RawMetricWitness_exists_time_defect_pos
  rw [c2RawGreenDefect_eq_material_norm_sq_sub] at ht
  exact ⟨t,by linarith⟩

theorem exists_c2_time_rawGreen_norm_gt :
    ∃ t : ℝ, ‖c2GlobalGreenInputIsometry t c2RawMetricWitness‖ <
      ‖canonicalRawGreenAnalysis (c2GlobalGreenInputIsometry t c2RawMetricWitness)‖ := by
  obtain ⟨t,ht⟩ := exists_c2_time_rawGreen_norm_sq_gt
  exact ⟨t,(sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ht⟩

theorem exists_c2_state_rawGreen_norm_gt :
    ∃ (t : ℝ) (f : State), f = c2GlobalGreenInputIsometry t c2RawMetricWitness ∧
      ‖f‖ < ‖canonicalRawGreenAnalysis f‖ := by
  obtain ⟨t,ht⟩ := exists_c2_time_rawGreen_norm_gt
  exact ⟨t,c2GlobalGreenInputIsometry t c2RawMetricWitness,rfl,ht⟩

theorem exists_c2_unit_state_rawGreen_norm_gt :
    ∃ (t : ℝ) (f : State), f = c2GlobalGreenInputIsometry t c2RawMetricWitness ∧
      ‖f‖ = 1 ∧ 1 < ‖canonicalRawGreenAnalysis f‖ := by
  obtain ⟨t,f,hf,ht⟩ := exists_c2_state_rawGreen_norm_gt
  have hn : ‖f‖ = 1 := by rw [hf, c2GlobalGreenInput_norm, c2RawMetricWitness_norm]
  exact ⟨t,f,hf,hn,by simpa only [hn] using ht⟩

theorem canonicalRawGreenAnalysis_not_isometry : ¬ Isometry canonicalRawGreenAnalysis := by
  intro h
  obtain ⟨t,f,hf,ht⟩ := exists_c2_state_rawGreen_norm_gt
  have he := h.dist_eq f 0
  rw [map_zero, dist_zero_right, dist_zero_right] at he
  exact (ne_of_gt ht) he

/-- A global nonidentity Gram witnessed by the authorized geometric input. -/
theorem canonicalRawGreen_frameOperator_ne_identity :
    frameOperator canonicalRawGreenAnalysis ≠ 1 := by
  intro hf
  apply canonicalRawGreenAnalysis_not_isometry
  apply (ContinuousLinearMap.isometry_iff_adjoint_comp_self canonicalRawGreenAnalysis).mpr
  exact hf


/-- Compatibility of the real and complex inner products follows from their
shared norm by the existing polarization identities, independent of instance packaging. -/
private theorem real_inner_complex_re {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [InnerProductSpace ℝ H] (x y : H) :
    inner ℝ x y = (inner ℂ x y).re := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  exact (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) x y).symm

private theorem rawGreen_adjoint_restrict_real :
    (canonicalRawGreenAnalysis.restrictScalars ℝ).adjoint =
      canonicalRawGreenAnalysis.adjoint.restrictScalars ℝ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ (canonicalRawGreenAnalysis.restrictScalars ℝ)).mpr
  intro y x
  change inner ℝ (canonicalRawGreenAnalysis.adjoint y) x = inner ℝ y (canonicalRawGreenAnalysis x)
  rw [real_inner_complex_re, real_inner_complex_re]
  exact congrArg Complex.re (canonicalRawGreenAnalysis.adjoint_inner_left x y)

/-- The real Gram used in the original bridge is the real restriction of F=T†T. -/
theorem rawGreen_realGram_eq_frameOperator_restrictScalars :
    (canonicalRawGreenAnalysis.restrictScalars ℝ).adjoint ∘L
      canonicalRawGreenAnalysis.restrictScalars ℝ =
      (frameOperator canonicalRawGreenAnalysis).restrictScalars ℝ := by
  rw [rawGreen_adjoint_restrict_real]
  rfl

/-- Reuse the existing compression after identifying the same global frame F. -/
theorem c2RestrictedGreenGram_eq_source_frame_compression (t : ℝ) :
    c2GlobalRestrictedGreenGram t =
      (c2GlobalGreenInputIsometry t).toContinuousLinearMap.adjoint ∘L
      (frameOperator canonicalRawGreenAnalysis).restrictScalars ℝ ∘L
      (c2GlobalGreenInputIsometry t).toContinuousLinearMap := by
  rw [c2GlobalRestrictedGreenGram_compression,
    rawGreen_realGram_eq_frameOperator_restrictScalars]

/-- Source factors stay real-linear; only F is packaged complex-linearly. -/
theorem c2RestrictedGreenGram_eq_W_J_frame_J_W (t : ℝ) :
    c2GlobalRestrictedGreenGram t =
      (globalCriticalPhysicalBranchIsometry t).toContinuousLinearMap.adjoint ∘L
      oddMaterialToGreenState.toContinuousLinearMap.adjoint ∘L
      (frameOperator canonicalRawGreenAnalysis).restrictScalars ℝ ∘L
      oddMaterialToGreenState.toContinuousLinearMap ∘L
      (globalCriticalPhysicalBranchIsometry t).toContinuousLinearMap := by
  rw [c2GlobalRestrictedGreenGram_source_factors,
    rawGreen_realGram_eq_frameOperator_restrictScalars]

/-- Restriction to the C2 source does not have uniform identity Gram in time. -/
theorem c2RestrictedGreenGram_not_uniform_identity :
    ¬ (∀ t : ℝ, c2GlobalRestrictedGreenGram t = 1) :=
  not_forall_restrictedGram_eq_identity

/-- Identity Gram is already present in the pure critical real branch. -/
theorem criticalBranch_gram_identity (t : ℝ) :
    (realCriticalBranchIsometry t).toContinuousLinearMap.adjoint ∘L
      (realCriticalBranchIsometry t).toContinuousLinearMap = 1 :=
  realCriticalBranch_adjoint_comp_self t

theorem globalPhysicalBranch_gram_identity (t : ℝ) :
    (globalCriticalPhysicalBranchIsometry t).toContinuousLinearMap.adjoint ∘L
      (globalCriticalPhysicalBranchIsometry t).toContinuousLinearMap = 1 :=
  c2GlobalSource_adjoint_comp_self t

theorem materialInclusion_gram_identity :
    oddMaterialToGreenState.toContinuousLinearMap.adjoint ∘L
      oddMaterialToGreenState.toContinuousLinearMap = 1 :=
  oddMaterialToGreenState_adjoint_comp_self

theorem c2GreenInput_gram_identity (t : ℝ) :
    (c2GlobalGreenInputIsometry t).toContinuousLinearMap.adjoint ∘L
      (c2GlobalGreenInputIsometry t).toContinuousLinearMap = 1 :=
  c2GlobalGreenInput_adjoint_comp_self t

theorem elementaryAtlas_gram_identity :
    canonicalCarryElementaryAtlas.toContinuousLinearMap.adjoint ∘L
      canonicalCarryElementaryAtlas.toContinuousLinearMap = 1 :=
  canonicalCarryElementaryAtlas.adjoint_comp_self

theorem preStencil_gram_identity :
    (preStencilLinearIsometry canonicalCarryInfinitePartition).toContinuousLinearMap.adjoint ∘L
      (preStencilLinearIsometry canonicalCarryInfinitePartition).toContinuousLinearMap = 1 :=
  (preStencilLinearIsometry canonicalCarryInfinitePartition).adjoint_comp_self

theorem c2PreStencil_gram_identity (t : ℝ) :
    (c2GlobalPreStencilIsometry t).toContinuousLinearMap.adjoint ∘L
      (c2GlobalPreStencilIsometry t).toContinuousLinearMap = 1 :=
  (c2GlobalPreStencilIsometry t).adjoint_comp_self

/-- The original stencil-localization identity remains the cause of the defect. -/
theorem c2RawMetricDefect_is_stencil_defect (t : ℝ) (V : CoreState) :
    c2GlobalRawGreenDefect t V =
      ‖greenAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t V)‖ ^ 2 -
      ‖directGreenAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t V)‖ ^ 2 :=
  c2GlobalRawGreenDefect_eq_stencil_defect t V

/-- The existing inverse square root normalizes the existing raw frame operator. -/
theorem canonicalRawGreen_inverseSqrt_normalization :
    inverseSqrtFrame canonicalRawGreenAnalysis ∘L frameOperator canonicalRawGreenAnalysis ∘L
      inverseSqrtFrame canonicalRawGreenAnalysis = 1 :=
  inverseSqrt_frameOperator_inverseSqrt canonicalRawGreenFrameBounds

theorem canonicalRawGreen_inverseSqrtFrame_ne_identity :
    inverseSqrtFrame canonicalRawGreenAnalysis ≠ 1 := by
  intro hq
  have hf := canonicalRawGreen_inverseSqrt_normalization
  rw [hq] at hf
  exact canonicalRawGreen_frameOperator_ne_identity (by
    simpa only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id] using hf)

/-- Literal reuse of the canonical normalization, not a new analysis definition. -/
theorem canonicalGreenAnalysis_eq_raw_comp_inverseSqrt :
    canonicalAnalysis canonicalRawGreenAnalysis =
      canonicalRawGreenAnalysis ∘L inverseSqrtFrame canonicalRawGreenAnalysis := rfl

theorem canonicalGreenAnalysis_gram_identity :
    (canonicalAnalysis canonicalRawGreenAnalysis).adjoint ∘L
      canonicalAnalysis canonicalRawGreenAnalysis = 1 :=
  canonicalAnalysis_adjoint_comp_self canonicalRawGreenFrameBounds

theorem canonicalGreenAnalysis_isometry : Isometry (canonicalAnalysis canonicalRawGreenAnalysis) :=
  canonicalAnalysis_isometry canonicalRawGreenFrameBounds

theorem canonicalGreenAnalysis_norm (f : State) :
    ‖canonicalAnalysis canonicalRawGreenAnalysis f‖ = ‖f‖ :=
  canonicalParseval_norm canonicalRawGreenFrameBounds f

/-- Equality would make the raw operator an isometry, contradicting the C2 witness. -/
theorem canonicalRawGreenAnalysis_ne_canonicalAnalysis :
    canonicalRawGreenAnalysis ≠ canonicalAnalysis canonicalRawGreenAnalysis := by
  intro h
  apply canonicalRawGreenAnalysis_not_isometry
  rw [h]
  exact canonicalGreenAnalysis_isometry

/-- Parseval normalization restores the metric also on the already isometric C2 input. -/
theorem canonicalC2GreenAnalysis_norm (t : ℝ) (V : CoreState) :
    ‖canonicalAnalysis canonicalRawGreenAnalysis (c2GlobalGreenInputIsometry t V)‖ = ‖V‖ := by
  rw [canonicalGreenAnalysis_norm, c2GlobalGreenInput_norm]

end GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
