import GeometryOfNumbers.Analysis.C2GlobalGreenBridge
import GreenFrame.Concrete.Analysis.ElementaryAtlasIsometry
import GreenFrame.Concrete.Analysis.CanonicalTowerChart

/-!
# Conservative transmission before the vertical stencil

The source and existing seed/return channels are reused verbatim. Only the
transmitted Green channel is varied. No frame normalization is performed.
-/

noncomputable section
open scoped BigOperators ENNReal lp InnerProductSpace

namespace GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
open GreenFrame.Concrete GeometryOfNumbers.Analysis C2GlobalGreenBridge

/-- The existing transmitted amplitude, applied to the current value alone. -/
def directGreenCoordinate (omega : AdmissibleInfinitePartition)
    (e : GreenEvent) (f : State) : ℂ :=
  (greenAmplitude omega e : ℂ) * f (eventNumber e)

theorem directGreenCoordinate_normSq_eq (omega : AdmissibleInfinitePartition)
    (e : GreenEvent) (f : State) :
    Complex.normSq (directGreenCoordinate omega e f) =
      greenEventMass omega e * Complex.normSq (f (eventNumber e)) := by
  rw [directGreenCoordinate, Complex.normSq_mul, Complex.normSq_ofReal,
    ← pow_two, greenAmplitude_sq]

/-- Same mass as Green, extended to the full number/camera product. -/
def directGreenEnergyTerm (omega : AdmissibleInfinitePartition)
    (f : State) (p : PNat × ℕ) : ℝ :=
  omega.weight p.2 p.1 / baseReal p.2 * Complex.normSq (f p.1)

theorem directGreenEnergyTerm_nonneg (omega : AdmissibleInfinitePartition)
    (f : State) (p : PNat × ℕ) : 0 ≤ directGreenEnergyTerm omega f p :=
  mul_nonneg (div_nonneg (omega.weight_nonneg _ _) (baseReal_nonneg _))
    (Complex.normSq_nonneg _)

theorem directGreenEnergyTerm_summable (omega : AdmissibleInfinitePartition)
    (f : State) : Summable (directGreenEnergyTerm omega f) := by
  apply Summable.of_nonneg_of_le (directGreenEnergyTerm_nonneg omega f) _
    (elementaryAtlasEnergyTerm_summable omega f)
  intro p
  have hr : 1 / baseReal p.2 ≤ 1 := by
    have hhalf : 1 / baseReal p.2 ≤ (1 / 2 : ℝ) := by
      simpa only [baseReciprocal] using baseReciprocal_le_half p.2
    linarith
  have h := mul_le_of_le_one_right (omega.weight_nonneg p.2 p.1) hr
  apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
  simpa [directGreenEnergyTerm, elementaryAtlasEnergyTerm, div_eq_mul_inv] using h

theorem directGreenCoordinate_normSq_summable (omega : AdmissibleInfinitePartition)
    (f : State) : Summable (fun e => Complex.normSq (directGreenCoordinate omega e f)) := by
  have h := (directGreenEnergyTerm_summable omega f).comp_injective
    (Subtype.val_injective.comp eventDivisibilityEquiv.injective)
  apply h.congr
  intro e
  exact (directGreenCoordinate_normSq_eq omega e f).symm

/-- Literal transmitted coordinates in the original Green event space. -/
def directGreenAnalysis (omega : AdmissibleInfinitePartition)
    (f : State) : ℓ²(GreenEvent, ℂ) :=
  ⟨fun e => directGreenCoordinate omega e f, by
    apply memℓp_gen
    apply (directGreenCoordinate_normSq_summable omega f).congr
    intro e
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (Complex.sq_norm (directGreenCoordinate omega e f)).symm⟩

@[simp] theorem directGreenAnalysis_apply (omega : AdmissibleInfinitePartition)
    (f : State) (e : GreenEvent) :
    directGreenAnalysis omega f e = directGreenCoordinate omega e f := rfl

theorem directGreenAnalysis_norm_sq_eq (omega : AdmissibleInfinitePartition)
    (f : State) : ‖directGreenAnalysis omega f‖ ^ 2 =
      ∑' p : PNat × ℕ, directGreenEnergyTerm omega f p := by
  rw [← residualL2_normSq_tsum_eq_norm_sq]
  calc
    (∑' e : GreenEvent, Complex.normSq (directGreenAnalysis omega f e)) =
        ∑' e : GreenEvent, directGreenEnergyTerm omega f (eventNumber e, e.1) := by
      apply tsum_congr
      intro e
      exact directGreenCoordinate_normSq_eq omega e f
    _ = ∑' p : PNat × ℕ, directGreenEnergyTerm omega f p := by
      apply tsum_greenEvent_reindex (fun n r => directGreenEnergyTerm omega f (n, r))
      intro n r h
      apply omega.support_dvd
      intro hz
      apply h
      simp [directGreenEnergyTerm, hz]

/-- The indexed infinite-camera version of the existing conservative mass split. -/
theorem directGreenMass_add_residualEventMass (omega : AdmissibleInfinitePartition)
    (r : ℕ) (n : PNat) :
    omega.weight r n / baseReal r + residualEventMass omega r n = omega.weight r n := by
  unfold residualEventMass residualFactor baseReciprocal
  ring

/-- Canonical specialization consumes the previously proved arithmetic split verbatim. -/
theorem canonicalDirectGreenMass_add_residualEventMass (r : ℕ) (n : PNat) :
    canonicalCarryInfinitePartition.weight r n / baseReal r +
      residualEventMass canonicalCarryInfinitePartition r n =
      canonicalCarryInfinitePartition.weight r n := by
  simpa only [greenMass, residualMass, carryPartition, baseReal_def,
    canonicalCarryInfinitePartition_weight, residualEventMass, residualFactor,
    baseReciprocal] using greenMass_add_residualMass carryPartition (baseNat r) (n : ℕ)

/-- Green transmission plus return is exactly the elementary camera energy. -/
theorem directGreen_add_residual_eq_elementaryCamera (omega : AdmissibleInfinitePartition)
    (f : State) :
    ‖directGreenAnalysis omega f‖ ^ 2 + ‖residualAnalysis omega f‖ ^ 2 =
      ‖elementaryAtlasCamera omega f‖ ^ 2 := by
  have hR : ‖residualAnalysis omega f‖ ^ 2 =
      ∑' p : PNat × ℕ, residualEnergyTerm omega f p := by
    rw [residualAnalysis_norm_sq_eq_camera_tsum,
      (residualEnergyTerm_summable omega f).tsum_prod]
    apply tsum_congr
    intro n
    simp only [residualEnergyDensity, residualCameraMass, residualEnergyTerm, tsum_mul_right]
  have hA : ‖elementaryAtlasCamera omega f‖ ^ 2 =
      ∑' p : PNat × ℕ, elementaryAtlasEnergyTerm omega f p := by
    rw [elementaryAtlasCamera_norm_sq_eq,
      (elementaryAtlasEnergyTerm_summable omega f).tsum_prod]
    rfl
  rw [directGreenAnalysis_norm_sq_eq, hR, hA,
    ← (directGreenEnergyTerm_summable omega f).tsum_add (residualEnergyTerm_summable omega f)]
  apply tsum_congr
  intro p
  change (omega.weight p.2 p.1 / baseReal p.2) * Complex.normSq (f p.1) +
    residualEventMass omega p.2 p.1 * Complex.normSq (f p.1) =
    omega.weight p.2 p.1 * Complex.normSq (f p.1)
  rw [← add_mul, directGreenMass_add_residualEventMass]

abbrev PreStencilSpace := WithLp 2 (SeedResidualSpace × ℓ²(GreenEvent, ℂ))

/-- Exactly the existing seed/return coordinates and the direct transmitted channel. -/
def preStencilAnalysis (omega : AdmissibleInfinitePartition) (f : State) : PreStencilSpace :=
  WithLp.toLp 2 (seedResidualAnalysis omega f, directGreenAnalysis omega f)

theorem preStencilAnalysis_norm_sq_eq_components (omega : AdmissibleInfinitePartition)
    (f : State) : ‖preStencilAnalysis omega f‖ ^ 2 =
      ‖seedResidualAnalysis omega f‖ ^ 2 + ‖directGreenAnalysis omega f‖ ^ 2 := by
  simpa [preStencilAnalysis] using WithLp.prod_norm_sq_eq_of_L2 (preStencilAnalysis omega f)

/-- Conservation is composed with the already proved elementary atlas isometry. -/
theorem preStencilAnalysis_norm_sq_eq (omega : AdmissibleInfinitePartition)
    (f : State) : ‖preStencilAnalysis omega f‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [preStencilAnalysis_norm_sq_eq_components, seedResidualAnalysis_norm_sq_eq]
  have h := directGreen_add_residual_eq_elementaryCamera omega f
  have hA := elementaryAtlas_norm_sq_eq_components omega f
  have hI := elementaryAtlas_norm_sq_eq omega f
  linarith

theorem preStencilAnalysis_norm (omega : AdmissibleInfinitePartition)
    (f : State) : ‖preStencilAnalysis omega f‖ = ‖f‖ := by
  nlinarith [preStencilAnalysis_norm_sq_eq omega f, norm_nonneg (preStencilAnalysis omega f),
    norm_nonneg f]

theorem directGreenAnalysis_add (omega : AdmissibleInfinitePartition) (f g : State) :
    directGreenAnalysis omega (f + g) = directGreenAnalysis omega f + directGreenAnalysis omega g := by
  apply lp.ext
  funext e
  simp [directGreenAnalysis_apply, directGreenCoordinate, mul_add]

theorem directGreenAnalysis_smul (omega : AdmissibleInfinitePartition) (c : ℂ) (f : State) :
    directGreenAnalysis omega (c • f) = c • directGreenAnalysis omega f := by
  apply lp.ext
  funext e
  simp [directGreenAnalysis_apply, directGreenCoordinate, smul_eq_mul, mul_left_comm]

/-- The direct channel is bounded before adding seed and return. -/
theorem directGreenAnalysis_norm_le (omega : AdmissibleInfinitePartition) (f : State) :
    ‖directGreenAnalysis omega f‖ ≤ ‖f‖ := by
  have h := preStencilAnalysis_norm_sq_eq_components omega f
  rw [preStencilAnalysis_norm_sq_eq] at h
  nlinarith [sq_nonneg ‖seedResidualAnalysis omega f‖,
    norm_nonneg (directGreenAnalysis omega f), norm_nonneg f]

def directGreenAnalysisLinearMap (omega : AdmissibleInfinitePartition) :
    State →ₗ[ℂ] ℓ²(GreenEvent, ℂ) where
  toFun := directGreenAnalysis omega
  map_add' := directGreenAnalysis_add omega
  map_smul' := directGreenAnalysis_smul omega

def directGreenAnalysisOperator (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] ℓ²(GreenEvent, ℂ) :=
  (directGreenAnalysisLinearMap omega).mkContinuous 1 fun f => by
    change ‖directGreenAnalysis omega f‖ ≤ 1 * ‖f‖
    simpa using directGreenAnalysis_norm_le omega f

theorem preStencilAnalysis_add (omega : AdmissibleInfinitePartition) (f g : State) :
    preStencilAnalysis omega (f + g) = preStencilAnalysis omega f + preStencilAnalysis omega g := by
  apply WithLp.ofLp_injective 2
  simp [preStencilAnalysis, seedResidualAnalysis_add, directGreenAnalysis_add]

theorem preStencilAnalysis_smul (omega : AdmissibleInfinitePartition) (c : ℂ) (f : State) :
    preStencilAnalysis omega (c • f) = c • preStencilAnalysis omega f := by
  apply WithLp.ofLp_injective 2
  simp [preStencilAnalysis, seedResidualAnalysis_smul, directGreenAnalysis_smul]

def preStencilLinearIsometry (omega : AdmissibleInfinitePartition) :
    State →ₗᵢ[ℂ] PreStencilSpace where
  toFun := preStencilAnalysis omega
  map_add' := preStencilAnalysis_add omega
  map_smul' := preStencilAnalysis_smul omega
  norm_map' := preStencilAnalysis_norm omega

/-- Real scalar restriction changes no coordinates or metric. -/
def preStencilRealLinearIsometry (omega : AdmissibleInfinitePartition) :
    State →ₗᵢ[ℝ] PreStencilSpace where
  toLinearMap := (preStencilLinearIsometry omega).toLinearMap.restrictScalars ℝ
  norm_map' := preStencilAnalysis_norm omega

/-- Composition with the provenance-correct global C2 source; no normalization. -/
def c2GlobalPreStencilIsometry (t : ℝ) : CoreState →ₗᵢ[ℝ] PreStencilSpace :=
  (preStencilRealLinearIsometry canonicalCarryInfinitePartition).comp
    (c2GlobalGreenInputIsometry t)

@[simp] theorem c2GlobalPreStencil_apply (t : ℝ) (V : CoreState) :
    c2GlobalPreStencilIsometry t V =
      preStencilAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t V) := rfl

theorem c2GlobalPreStencil_norm (t : ℝ) (V : CoreState) :
    ‖c2GlobalPreStencilIsometry t V‖ = ‖V‖ :=
  (c2GlobalPreStencilIsometry t).norm_map V

/-- Conditional second ancestor is inherited without modification. -/
def greenStencilCorrection (omega : AdmissibleInfinitePartition)
    (e : GreenEvent) (f : State) : ℂ :=
  (greenAmplitude omega e : ℂ) * (parentTerm e f + grandparentTerm e f)

theorem greenCoordinate_eq_direct_add_ancestorCorrection (omega : AdmissibleInfinitePartition)
    (e : GreenEvent) (f : State) :
    greenCoordinate omega e f = directGreenCoordinate omega e f + greenStencilCorrection omega e f := by
  unfold greenCoordinate directGreenCoordinate greenStencilCorrection verticalGreenStencil currentTerm
  ring

theorem greenStencilCorrection_eq (omega : AdmissibleInfinitePartition)
    (e : GreenEvent) (f : State) :
    greenStencilCorrection omega e f = (greenAmplitude omega e : ℂ) *
      (-((2 * carryRatio e.1 : ℝ) : ℂ) * f e.2 +
        if HasGrandparent e then ((carryRatio e.1 ^ 2 : ℝ) : ℂ) * f (grandparentIndex e) else 0) := by
  simp [greenStencilCorrection, parentTerm, grandparentTerm, neg_mul]

/-- Bundled correction exists as the difference of two existing L² vectors. -/
def greenStencilCorrectionAnalysis (omega : AdmissibleInfinitePartition)
    (f : State) : ℓ²(GreenEvent, ℂ) :=
  greenAnalysis omega f - directGreenAnalysis omega f

theorem greenStencilCorrectionAnalysis_apply (omega : AdmissibleInfinitePartition)
    (f : State) (e : GreenEvent) :
    greenStencilCorrectionAnalysis omega f e = greenStencilCorrection omega e f := by
  change greenCoordinate omega e f - directGreenCoordinate omega e f = _
  rw [greenCoordinate_eq_direct_add_ancestorCorrection]
  ring

/-- Bounded correction uses only the difference of the two channel operators. -/
def greenStencilCorrectionOperator (omega : AdmissibleInfinitePartition) :
    State →L[ℂ] ℓ²(GreenEvent, ℂ) :=
  greenAnalysisOperator omega - directGreenAnalysisOperator omega

@[simp] theorem greenStencilCorrectionOperator_apply (omega : AdmissibleInfinitePartition)
    (f : State) : greenStencilCorrectionOperator omega f = greenStencilCorrectionAnalysis omega f := rfl

/-- Exact localization; no sign or nonvanishing of the defect is asserted. -/
theorem concreteAnalysis_norm_sq_sub_preStencil_norm_sq (omega : AdmissibleInfinitePartition)
    (f : State) :
    ‖concreteAnalysisOperator omega f‖ ^ 2 - ‖preStencilAnalysis omega f‖ ^ 2 =
      ‖greenAnalysis omega f‖ ^ 2 - ‖directGreenAnalysis omega f‖ ^ 2 := by
  rw [concreteAnalysisOperator_norm_sq_eq_seedResidual_add_green,
    preStencilAnalysis_norm_sq_eq_components]
  ring

theorem concreteAnalysis_norm_defect_eq_stencil_defect (omega : AdmissibleInfinitePartition)
    (f : State) :
    ‖concreteAnalysisOperator omega f‖ ^ 2 - ‖f‖ ^ 2 =
      ‖greenAnalysis omega f‖ ^ 2 - ‖directGreenAnalysis omega f‖ ^ 2 := by
  rw [← preStencilAnalysis_norm_sq_eq omega f]
  exact concreteAnalysis_norm_sq_sub_preStencil_norm_sq omega f

theorem c2GlobalRawGreenDefect_eq_stencil_defect (t : ℝ) (V : CoreState) :
    c2GlobalRawGreenDefect t V =
      ‖greenAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t V)‖ ^ 2 -
      ‖directGreenAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t V)‖ ^ 2 := by
  unfold c2GlobalRawGreenDefect
  rw [c2GlobalGreenAnalysis_apply, ← c2GlobalGreenInput_norm t V]
  exact concreteAnalysis_norm_defect_eq_stencil_defect _ _

/-- The restricted Gram quadratic defect is localized to this same channel replacement. -/
theorem c2GlobalRestrictedGreenGram_stencil_defect (t : ℝ) (V : CoreState) :
    inner ℝ ((c2GlobalRestrictedGreenGram t - 1) V) V =
      ‖greenAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t V)‖ ^ 2 -
      ‖directGreenAnalysis canonicalCarryInfinitePartition (c2GlobalGreenInputIsometry t V)‖ ^ 2 := by
  rw [← c2GlobalRawGreenDefect_eq_gram_defect]
  exact c2GlobalRawGreenDefect_eq_stencil_defect t V

end GeometryOfNumbers.Analysis.C2GreenPreStencilCanary
