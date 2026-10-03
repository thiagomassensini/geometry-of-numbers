import GeometryOfNumbers.Analysis.C2GlobalPhysicalBranchCanary
import GreenFrame.Concrete.Analysis.ConcreteSplitBounds
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Provenance-correct global C2 source in the raw concrete Green analysis

GeometryOfNumbers remains real. Complex packaging starts only here, as two
coordinate fields, without changing upstream amplitude or phase. The raw Green
map is restricted to real scalars; no Parseval normalization is used.
-/
open scoped BigOperators ENNReal NNReal lp InnerProductSpace
namespace GeometryOfNumbers.Analysis.C2GlobalGreenBridge
open GeometryOfNumbers.Analysis GreenFrame.Concrete
noncomputable section

private def planePackagingLinear : RealPlaneHilbert →ₗ[ℝ] ℂ where
  toFun v := ⟨v 0, v 1⟩
  map_add' v w := rfl
  map_smul' c v := by
    apply Complex.ext <;> simp

private theorem planePackagingLinear_norm (v : RealPlaneHilbert) :
    ‖planePackagingLinear v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm]
  have he := realPlaneHilbert_energy_eq_norm_sq v
  change (v 0)^2 + (v 1)^2 = ‖v‖^2 at he
  change v 0 * v 0 + v 1 * v 1 = ‖v‖ ^ 2
  simpa only [pow_two] using he

def realPlaneToComplexIsometry : RealPlaneHilbert →ₗᵢ[ℝ] ℂ :=
  { planePackagingLinear with norm_map' := planePackagingLinear_norm }

theorem realPlaneToComplexIsometry_re (v : RealPlaneHilbert) :
    (realPlaneToComplexIsometry v).re = v 0 := rfl

theorem realPlaneToComplexIsometry_im (v : RealPlaneHilbert) :
    (realPlaneToComplexIsometry v).im = v 1 := rfl

theorem realPlaneToComplexIsometry_normSq (v : RealPlaneHilbert) :
    Complex.normSq (realPlaneToComplexIsometry v) =
      realPlaneEnergy (realPlaneHilbertEquiv.symm v) := by
  rw [← Complex.sq_norm, LinearIsometry.norm_map, realPlaneHilbert_energy_eq_norm_sq]

def oddMaterialGreenCoordinates (x : OddMaterialState) : PNat → ℂ :=
  Function.extend (Subtype.val : OddMaterialIndex → PNat)
    (fun n => realPlaneToComplexIsometry (x n)) 0

private theorem inclusion_square_extend (x : OddMaterialState) :
    (fun n => ‖oddMaterialGreenCoordinates x n‖ ^ 2) =
      Function.extend (Subtype.val : OddMaterialIndex → PNat) (fun n => ‖x n‖ ^ 2) 0 := by
  funext n
  by_cases h : ∃ i : OddMaterialIndex, i.val = n
  · rcases h with ⟨i,rfl⟩
    simp [oddMaterialGreenCoordinates]
  · simp [oddMaterialGreenCoordinates, Function.extend_apply' _ _ _ h]

private def inclusionElement (x : OddMaterialState) : State :=
  ⟨oddMaterialGreenCoordinates x, by
    change Memℓp (oddMaterialGreenCoordinates x) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [inclusion_square_extend]
    exact (summable_extend_zero (Subtype.val_injective :
      Function.Injective (Subtype.val : OddMaterialIndex → PNat))).mpr
      (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩

private def inclusionLinear : OddMaterialState →ₗ[ℝ] State where
  toFun := inclusionElement
  map_add' x y := by
    ext n
    by_cases h : ∃ i : OddMaterialIndex, i.val = n
    · rcases h with ⟨i,rfl⟩
      simp [inclusionElement, oddMaterialGreenCoordinates, map_add]
    · simp [inclusionElement, oddMaterialGreenCoordinates, Function.extend_apply' _ _ _ h]
  map_smul' c x := by
    ext n
    by_cases h : ∃ i : OddMaterialIndex, i.val = n
    · rcases h with ⟨i,rfl⟩
      simp [inclusionElement, oddMaterialGreenCoordinates, map_smul]
    · simp [inclusionElement, oddMaterialGreenCoordinates, Function.extend_apply' _ _ _ h]

private theorem inclusionElement_norm (x : OddMaterialState) : ‖inclusionElement x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hx := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  have hy := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (inclusionElement x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  rw [hy, hx]
  change (∑' n : PNat, ‖oddMaterialGreenCoordinates x n‖ ^ 2) = _
  rw [inclusion_square_extend, tsum_extend_zero
    (Subtype.val_injective : Function.Injective (Subtype.val : OddMaterialIndex → PNat))]

def oddMaterialToGreenState : OddMaterialState →ₗᵢ[ℝ] State :=
  { inclusionLinear with norm_map' := inclusionElement_norm }

theorem oddMaterialToGreenState_apply (x : OddMaterialState) (n : OddMaterialIndex) :
    oddMaterialToGreenState x n.val = realPlaneToComplexIsometry (x n) :=
  by
    change oddMaterialGreenCoordinates x n.val = _
    exact Subtype.val_injective.extend_apply _ _ n

theorem oddMaterialToGreenState_apply_off_sector (x : OddMaterialState) (n : PNat)
    (h : ¬ (Odd (n : ℕ) ∧ 3 ≤ (n : ℕ))) : oddMaterialToGreenState x n = 0 := by
  change Function.extend (Subtype.val : OddMaterialIndex → PNat)
    (fun i => realPlaneToComplexIsometry (x i)) 0 n = 0
  apply Function.extend_apply'
  rintro ⟨i,rfl⟩
  exact h i.property

theorem oddMaterialToGreenState_one (x : OddMaterialState) :
    oddMaterialToGreenState x 1 = 0 := by
  apply oddMaterialToGreenState_apply_off_sector
  norm_num

theorem oddMaterialToGreenState_even (x : OddMaterialState) (n : PNat)
    (h : Even (n : ℕ)) : oddMaterialToGreenState x n = 0 := by
  apply oddMaterialToGreenState_apply_off_sector
  exact fun hn => (Nat.not_even_iff_odd.mpr hn.1) h

theorem oddMaterialToGreenState_norm (x : OddMaterialState) :
    ‖oddMaterialToGreenState x‖ = ‖x‖ := oddMaterialToGreenState.norm_map x

def c2GlobalGreenInputIsometry (t : ℝ) : CoreState →ₗᵢ[ℝ] State :=
  oddMaterialToGreenState.comp (globalCriticalPhysicalBranchIsometry t)

theorem c2GlobalGreenInput_norm (t : ℝ) (v : CoreState) :
    ‖c2GlobalGreenInputIsometry t v‖ = ‖v‖ := (c2GlobalGreenInputIsometry t).norm_map v

theorem c2GlobalGreenInput_apply (t : ℝ) (v : CoreState) (n : OddMaterialIndex) :
    c2GlobalGreenInputIsometry t v n.val = realPlaneToComplexIsometry
      (realPlaneHilbertEquiv
        (scaleRealPlane ((2 : ℝ) ^ (-(c2BranchDepth (oddMaterialC2Address n).2 : ℝ) / 2))
          (rotateRealPlane (-t * Real.log ((n.val : ℕ) : ℝ))
            (realPlaneHilbertEquiv.symm (v (oddMaterialC2Address n).1))))) := by
  change oddMaterialToGreenState (globalCriticalPhysicalBranchIsometry t v) n.val = _
  rw [oddMaterialToGreenState_apply]
  apply congrArg realPlaneToComplexIsometry
  rw [← globalCriticalPhysicalBranchIsometry_pointwise t v n,
    LinearEquiv.apply_symm_apply]

theorem c2GlobalGreenInput_one (t : ℝ) (v : CoreState) : c2GlobalGreenInputIsometry t v 1 = 0 :=
  oddMaterialToGreenState_one _

theorem c2GlobalGreenInput_even (t : ℝ) (v : CoreState) (n : PNat) (h : Even (n : ℕ)) :
    c2GlobalGreenInputIsometry t v n = 0 := oddMaterialToGreenState_even _ n h

/-- The material address and all upstream decoded fields remain unchanged;
packaging is injective in the two real quadratures. -/
theorem c2GlobalGreenInput_provenance (t : ℝ) (v : CoreState) (i : GlobalC2BranchAddress) :
    c2GlobalGreenInputIsometry t v (globalC2MaterialAddress i) =
      realPlaneToComplexIsometry (globalCriticalPhysicalBranchIsometry t v
        (globalC2OddMaterialAddress i)) ∧
    oddMaterialC2Address (globalC2OddMaterialAddress i) = i :=
  by
    constructor
    · change oddMaterialToGreenState (globalCriticalPhysicalBranchIsometry t v)
        (globalC2OddMaterialAddress i).val = _
      exact oddMaterialToGreenState_apply _ _
    · exact oddMaterialC2Address_encode i

/-- Fixed canonical Green partition, with the source kept real-linear. -/
def c2GlobalGreenAnalysis (t : ℝ) : CoreState →L[ℝ] ConcreteAnalysisSpace :=
  ((concreteAnalysisOperator canonicalCarryInfinitePartition).restrictScalars ℝ).comp
    (c2GlobalGreenInputIsometry t).toContinuousLinearMap

theorem c2GlobalGreenAnalysis_apply (t : ℝ) (v : CoreState) :
    c2GlobalGreenAnalysis t v = concreteAnalysisOperator canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t v) := rfl

theorem c2GlobalGreenAnalysis_norm_sq_bounds (t : ℝ) (v : CoreState) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ ‖c2GlobalGreenAnalysis t v‖ ^ 2 ∧
    ‖c2GlobalGreenAnalysis t v‖ ^ 2 ≤ (1 + greenBesselConstant) * ‖v‖ ^ 2 := by
  simpa only [c2GlobalGreenAnalysis_apply, c2GlobalGreenInput_norm] using
    concreteAnalysisOperator_norm_sq_bounds canonicalCarryInfinitePartition
      (c2GlobalGreenInputIsometry t v)

theorem c2GlobalGreenAnalysis_split_seedResidual_green (t : ℝ) (v : CoreState) :
    ‖c2GlobalGreenAnalysis t v‖ ^ 2 =
      ‖seedResidualAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 +
      ‖greenAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 :=
  concreteAnalysisOperator_norm_sq_eq_seedResidual_add_green _ _

theorem c2GlobalGreenAnalysis_split_external_bulk (t : ℝ) (v : CoreState) :
    ‖c2GlobalGreenAnalysis t v‖ ^ 2 =
      ‖concreteExternalAnalysisOperator canonicalCarryInfinitePartition
        (c2GlobalGreenInputIsometry t v)‖ ^ 2 +
      ‖greenBulkSectorAnalysis canonicalCarryInfinitePartition
        (c2GlobalGreenInputIsometry t v)‖ ^ 2 :=
  concreteAnalysisOperator_norm_sq_eq_external_add_bulk _ _

theorem c2GlobalGreenAnalysis_split_three (t : ℝ) (v : CoreState) :
    ‖c2GlobalGreenAnalysis t v‖ ^ 2 =
      ‖seedResidualAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 +
      ‖greenDepthOneSectorAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 +
      ‖greenBulkSectorAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 := by
  rw [c2GlobalGreenAnalysis_split_external_bulk,
    concreteExternalAnalysisOperator_norm_sq_eq]

def c2GlobalRawGreenDefect (t : ℝ) (v : CoreState) : ℝ :=
  ‖c2GlobalGreenAnalysis t v‖ ^ 2 - ‖v‖ ^ 2

/-- Explicit scalar-clock packaging of an already-defined real rotation. -/
theorem realPlaneToComplexIsometry_scale_rotate (a theta : ℝ) (v : RealPlaneState) :
    realPlaneToComplexIsometry (realPlaneHilbertEquiv (scaleRealPlane a (rotateRealPlane theta v))) =
      (a : ℂ) * (⟨Real.cos theta, Real.sin theta⟩ : ℂ) *
        realPlaneToComplexIsometry (realPlaneHilbertEquiv v) := by
  apply Complex.ext <;>
    simp [realPlaneToComplexIsometry, planePackagingLinear, realPlaneHilbertEquiv,
      scaleRealPlane, rotateRealPlane, Complex.mul_re, Complex.mul_im] <;> ring

theorem realPlaneToComplexIsometry_coordinate_roundtrip (v : RealPlaneHilbert) :
    realPlaneHilbertEquiv.symm v =
      ((realPlaneToComplexIsometry v).re, (realPlaneToComplexIsometry v).im) := rfl

theorem c2GlobalGreenInput_closed_form (t : ℝ) (v : CoreState) (n : OddMaterialIndex) :
    c2GlobalGreenInputIsometry t v n.val =
      (((2 : ℝ) ^ (-(c2BranchDepth (oddMaterialC2Address n).2 : ℝ) / 2) : ℝ) : ℂ) *
        (⟨Real.cos (-t * Real.log ((n.val : ℕ) : ℝ)),
          Real.sin (-t * Real.log ((n.val : ℕ) : ℝ))⟩ : ℂ) *
        realPlaneToComplexIsometry (v (oddMaterialC2Address n).1) := by
  rw [c2GlobalGreenInput_apply, realPlaneToComplexIsometry_scale_rotate,
    LinearEquiv.apply_symm_apply]

/-- Exact raw energy defect, with no assertion that it vanishes. -/
theorem c2GlobalRawGreenDefect_split (t : ℝ) (v : CoreState) :
    c2GlobalRawGreenDefect t v =
      ‖seedResidualAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 +
      ‖greenAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 - ‖v‖ ^ 2 := by
  rw [c2GlobalRawGreenDefect, c2GlobalGreenAnalysis_split_seedResidual_green]

theorem c2GlobalRawGreenDefect_bounds (t : ℝ) (v : CoreState) :
    -(1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ c2GlobalRawGreenDefect t v ∧
      c2GlobalRawGreenDefect t v ≤ greenBesselConstant * ‖v‖ ^ 2 := by
  have h := c2GlobalGreenAnalysis_norm_sq_bounds t v
  unfold c2GlobalRawGreenDefect
  constructor <;> nlinarith

/-- The Gram of the real-linear restriction, before any normalization. -/
def c2GlobalRestrictedGreenGram (t : ℝ) : CoreState →L[ℝ] CoreState :=
  (c2GlobalGreenAnalysis t).adjoint ∘L c2GlobalGreenAnalysis t

theorem c2GlobalRestrictedGreenGram_inner (t : ℝ) (v : CoreState) :
    inner ℝ (c2GlobalRestrictedGreenGram t v) v = ‖c2GlobalGreenAnalysis t v‖ ^ 2 := by
  change inner ℝ ((c2GlobalGreenAnalysis t).adjoint (c2GlobalGreenAnalysis t v)) v = _
  rw [(c2GlobalGreenAnalysis t).adjoint_inner_left, real_inner_self_eq_norm_sq]

theorem c2GlobalRestrictedGreenGram_positive (t : ℝ) :
    (c2GlobalRestrictedGreenGram t).IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self (c2GlobalGreenAnalysis t)

theorem c2GlobalRestrictedGreenGram_bounds (t : ℝ) (v : CoreState) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ inner ℝ (c2GlobalRestrictedGreenGram t v) v ∧
    inner ℝ (c2GlobalRestrictedGreenGram t v) v ≤ (1 + greenBesselConstant) * ‖v‖ ^ 2 := by
  rw [c2GlobalRestrictedGreenGram_inner]
  exact c2GlobalGreenAnalysis_norm_sq_bounds t v

theorem c2GlobalRestrictedGreenGram_isUnit (t : ℝ) : IsUnit (c2GlobalRestrictedGreenGram t) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (c2GlobalRestrictedGreenGram t) (c := (1 / 2 : ℝ≥0)) (by norm_num)
  intro v
  change ‖v‖ ^ 2 * (1 / 2 : ℝ) ≤ ‖inner ℝ (c2GlobalRestrictedGreenGram t v) v‖
  rw [c2GlobalRestrictedGreenGram_inner, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [(c2GlobalGreenAnalysis_norm_sq_bounds t v).1]

theorem c2GlobalRestrictedGreenGram_bijective (t : ℝ) :
    Function.Bijective (c2GlobalRestrictedGreenGram t) :=
  ContinuousLinearMap.isUnit_iff_bijective.mp (c2GlobalRestrictedGreenGram_isUnit t)

theorem c2GlobalRestrictedGreenGram_strictlyPositive (t : ℝ) :
    IsStrictlyPositive (c2GlobalRestrictedGreenGram t) :=
  (c2GlobalRestrictedGreenGram_isUnit t).isStrictlyPositive
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr (c2GlobalRestrictedGreenGram_positive t))

/-- All additional Gram comes from the raw Green analysis restricted to the
isometric input's range. -/
theorem c2GlobalRestrictedGreenGram_compression (t : ℝ) :
    c2GlobalRestrictedGreenGram t =
      (c2GlobalGreenInputIsometry t).toContinuousLinearMap.adjoint ∘L
      (((concreteAnalysisOperator canonicalCarryInfinitePartition).restrictScalars ℝ).adjoint ∘L
        (concreteAnalysisOperator canonicalCarryInfinitePartition).restrictScalars ℝ) ∘L
      (c2GlobalGreenInputIsometry t).toContinuousLinearMap := by
  rw [c2GlobalRestrictedGreenGram, c2GlobalGreenAnalysis, ContinuousLinearMap.adjoint_comp]
  rfl

theorem c2GlobalRestrictedGreenGram_source_factors (t : ℝ) :
    c2GlobalRestrictedGreenGram t =
      (globalCriticalPhysicalBranchIsometry t).toContinuousLinearMap.adjoint ∘L
      oddMaterialToGreenState.toContinuousLinearMap.adjoint ∘L
      (((concreteAnalysisOperator canonicalCarryInfinitePartition).restrictScalars ℝ).adjoint ∘L
        (concreteAnalysisOperator canonicalCarryInfinitePartition).restrictScalars ℝ) ∘L
      oddMaterialToGreenState.toContinuousLinearMap ∘L
      (globalCriticalPhysicalBranchIsometry t).toContinuousLinearMap := by
  rw [c2GlobalRestrictedGreenGram_compression]
  have hb : (c2GlobalGreenInputIsometry t).toContinuousLinearMap =
      oddMaterialToGreenState.toContinuousLinearMap ∘L
        (globalCriticalPhysicalBranchIsometry t).toContinuousLinearMap := by
    ext v n
    rfl
  rw [hb, ContinuousLinearMap.adjoint_comp]
  rfl

theorem c2GlobalGreenInput_adjoint_comp_self (t : ℝ) :
    (c2GlobalGreenInputIsometry t).toContinuousLinearMap.adjoint ∘L
      (c2GlobalGreenInputIsometry t).toContinuousLinearMap = 1 :=
  (c2GlobalGreenInputIsometry t).adjoint_comp_self

theorem c2GlobalSource_adjoint_comp_self (t : ℝ) :
    (globalCriticalPhysicalBranchIsometry t).toContinuousLinearMap.adjoint ∘L
      (globalCriticalPhysicalBranchIsometry t).toContinuousLinearMap = 1 :=
  (globalCriticalPhysicalBranchIsometry t).adjoint_comp_self

theorem oddMaterialToGreenState_adjoint_comp_self :
    oddMaterialToGreenState.toContinuousLinearMap.adjoint ∘L
      oddMaterialToGreenState.toContinuousLinearMap = 1 := oddMaterialToGreenState.adjoint_comp_self

theorem c2GlobalRawGreenDefect_eq_gram_defect (t : ℝ) (v : CoreState) :
    c2GlobalRawGreenDefect t v = inner ℝ ((c2GlobalRestrictedGreenGram t - 1) v) v := by
  rw [sub_apply, one_apply_eq_self, inner_sub_left,
    c2GlobalRestrictedGreenGram_inner, real_inner_self_eq_norm_sq]
  rfl

/-- This is a criterion, not a proof that the raw Gram is identity. -/
theorem c2GlobalRestrictedGreenGram_eq_one_iff_norm (t : ℝ) :
    c2GlobalRestrictedGreenGram t = 1 ↔
      ∀ v : CoreState, ‖c2GlobalGreenAnalysis t v‖ = ‖v‖ := by
  constructor
  · intro h v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hi := c2GlobalRestrictedGreenGram_inner t v
    rw [h, one_apply_eq_self, real_inner_self_eq_norm_sq] at hi
    exact hi.symm
  · intro h
    let f : CoreState →ₗᵢ[ℝ] ConcreteAnalysisSpace :=
      { (c2GlobalGreenAnalysis t).toLinearMap with norm_map' := h }
    exact (ContinuousLinearMap.isometry_iff_adjoint_comp_self (c2GlobalGreenAnalysis t)).mp f.isometry

theorem c2GlobalRestrictedGreenGram_eq_one_iff_defect_zero (t : ℝ) :
    c2GlobalRestrictedGreenGram t = 1 ↔ ∀ v : CoreState, c2GlobalRawGreenDefect t v = 0 := by
  rw [c2GlobalRestrictedGreenGram_eq_one_iff_norm]
  constructor
  · intro h v
    simp only [c2GlobalRawGreenDefect, h v, sub_self]
  · intro h v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    exact sub_eq_zero.mp (h v)

/-- Both quadratures are recoverable at their unchanged odd material index. -/
theorem c2GlobalGreenInput_quadrature_roundtrip (t : ℝ) (v : CoreState) (n : OddMaterialIndex) :
    realPlaneHilbertEquiv.symm (globalCriticalPhysicalBranchIsometry t v n) =
      ((c2GlobalGreenInputIsometry t v n.val).re,
        (c2GlobalGreenInputIsometry t v n.val).im) := by
  change _ = ((oddMaterialToGreenState (globalCriticalPhysicalBranchIsometry t v) n.val).re,
    (oddMaterialToGreenState (globalCriticalPhysicalBranchIsometry t v) n.val).im)
  rw [oddMaterialToGreenState_apply]
  exact realPlaneToComplexIsometry_coordinate_roundtrip _

theorem c2GlobalGreenInput_seedResidual_eq_residual (t : ℝ) (v : CoreState) :
    ‖seedResidualAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 =
      ‖residualAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 := by
  rw [seedResidualAnalysis_norm_sq_eq, c2GlobalGreenInput_one]
  simp

theorem c2GlobalGreenAnalysis_split_residual_depthOne_bulk (t : ℝ) (v : CoreState) :
    ‖c2GlobalGreenAnalysis t v‖ ^ 2 =
      ‖residualAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 +
      ‖greenDepthOneSectorAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 +
      ‖greenBulkSectorAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t v)‖ ^ 2 := by
  rw [c2GlobalGreenAnalysis_split_three, c2GlobalGreenInput_seedResidual_eq_residual]

/-- In particular the defect is not claimed to be nonzero for every input. -/
theorem c2GlobalRawGreenDefect_zero (t : ℝ) : c2GlobalRawGreenDefect t 0 = 0 := by
  simp [c2GlobalRawGreenDefect]

end
end GeometryOfNumbers.Analysis.C2GlobalGreenBridge
