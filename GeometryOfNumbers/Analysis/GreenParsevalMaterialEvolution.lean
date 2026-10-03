import GeometryOfNumbers.Analysis.GreenStateMaterialEvolution

/-! Exact bounded material dynamics on the Parseval range, identity on its
orthogonal complement. Strong differentiation uses only the previous domain. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology lp InnerProduct
namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
open GreenFrame.Concrete GreenStateMaterialLog GreenParsevalMaterialLog
open GreenStateMaterialDynamics C2GlobalGreenBridge GeometryOfNumbers.Analysis
open UnitaryZeroExtension

def parsevalRangeMaterialEvolution (s : ℝ) : ParsevalRange ≃ₗᵢ[ℂ] ParsevalRange :=
  (parsevalRangeUnitary.symm.trans (greenStateMaterialEvolution s)).trans parsevalRangeUnitary

@[simp] theorem parsevalRangeMaterialEvolution_apply (s : ℝ) (y : ParsevalRange) :
    parsevalRangeMaterialEvolution s y =
      parsevalRangeUnitary (greenStateMaterialEvolution s (parsevalRangeUnitary.symm y)) := rfl

@[simp] theorem parsevalRangeMaterialEvolution_zero (y : ParsevalRange) :
    parsevalRangeMaterialEvolution 0 y = y := by simp

theorem parsevalRangeMaterialEvolution_add (s r : ℝ) (y : ParsevalRange) :
    parsevalRangeMaterialEvolution (s+r) y = parsevalRangeMaterialEvolution s (parsevalRangeMaterialEvolution r y) := by
  simp [greenStateMaterialEvolution_add]

private def productMaterialEvolution (s : ℝ) :
    WithLp 2 (ParsevalRange × ParsevalOrthogonal) ≃ₗᵢ[ℂ] WithLp 2 (ParsevalRange × ParsevalOrthogonal) :=
  LinearIsometryEquiv.withLpProdCongr 2 (parsevalRangeMaterialEvolution s)
    (LinearIsometryEquiv.refl ℂ ParsevalOrthogonal)

private theorem productMaterialEvolution_apply (s : ℝ)
    (z : WithLp 2 (ParsevalRange × ParsevalOrthogonal)) :
    productMaterialEvolution s z = WithLp.toLp 2
      (parsevalRangeMaterialEvolution s (WithLp.ofLp z).1, (WithLp.ofLp z).2) := rfl

/-- The SAME canonical Parseval range transport, with identity on the gauge sector. -/
def greenParsevalMaterialEvolution (s : ℝ) : ConcreteAnalysisSpace ≃ₗᵢ[ℂ] ConcreteAnalysisSpace :=
  (greenParsevalOrthogonalDecomposition.trans (productMaterialEvolution s)).trans
    greenParsevalOrthogonalDecomposition.symm

theorem greenParsevalMaterialEvolution_apply (s : ℝ) (y : ConcreteAnalysisSpace) :
    greenParsevalMaterialEvolution s y =
      (parsevalRangeMaterialEvolution s (parsevalRangeSubmodule.orthogonalProjectionOnto y) : ConcreteAnalysisSpace) +
        (parsevalRangeSubmoduleᗮ.orthogonalProjectionOnto y : ConcreteAnalysisSpace) := by
  simp [greenParsevalMaterialEvolution, productMaterialEvolution,
    greenParsevalOrthogonalDecomposition, Submodule.orthogonalDecomposition_apply]

/-- P* is exactly the inverse range coordinate after canonical orthogonal projection. -/
theorem parsevalRange_inverse_projection_eq_adjoint (y : ConcreteAnalysisSpace) :
    parsevalRangeUnitary.symm (parsevalRangeSubmodule.orthogonalProjectionOnto y) =
      greenParsevalAnalysis.adjoint y := by
  let x0 := parsevalRangeUnitary.symm (parsevalRangeSubmodule.orthogonalProjectionOnto y)
  have hp : greenParsevalAnalysis x0 = (parsevalRangeSubmodule.orthogonalProjectionOnto y : ConcreteAnalysisSpace) := by
    exact congrArg Subtype.val (parsevalRangeUnitary.apply_symm_apply (parsevalRangeSubmodule.orthogonalProjectionOnto y))
  have hg : greenParsevalAnalysis.adjoint (greenParsevalAnalysis x0) = x0 := by
    have h := congrArg (fun A : State →L[ℂ] State => A x0) greenParsevalAnalysis_gram_identity
    simpa using h
  apply ext_inner_left ℂ
  intro x
  calc
    _ = inner ℂ x (greenParsevalAnalysis.adjoint (greenParsevalAnalysis x0)) := by rw [hg]
    _ = inner ℂ (greenParsevalAnalysis x) (greenParsevalAnalysis x0) := greenParsevalAnalysis.adjoint_inner_right x _
    _ = inner ℂ (greenParsevalAnalysis x) y := by
      rw [hp]
      exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (parsevalRangeUnitary x) y
    _ = _ := (greenParsevalAnalysis.adjoint_inner_right x y).symm

theorem greenParsevalMaterialEvolution_apply_adjoint (s : ℝ) (y : ConcreteAnalysisSpace) :
    greenParsevalMaterialEvolution s y =
      greenParsevalAnalysis (greenStateMaterialEvolution s (greenParsevalAnalysis.adjoint y)) +
        (parsevalRangeSubmoduleᗮ.orthogonalProjectionOnto y : ConcreteAnalysisSpace) := by
  rw [greenParsevalMaterialEvolution_apply, parsevalRangeMaterialEvolution_apply,
    parsevalRangeUnitary_apply, parsevalRange_inverse_projection_eq_adjoint]

@[simp] theorem greenParsevalMaterialEvolution_norm (s : ℝ) (y : ConcreteAnalysisSpace) :
    ‖greenParsevalMaterialEvolution s y‖ = ‖y‖ := (greenParsevalMaterialEvolution s).norm_map y

private theorem evolution_decomposition (s : ℝ) (y : ConcreteAnalysisSpace) :
    greenParsevalOrthogonalDecomposition (greenParsevalMaterialEvolution s y) =
      productMaterialEvolution s (greenParsevalOrthogonalDecomposition y) := by
  simp [greenParsevalMaterialEvolution]

@[simp] theorem greenParsevalMaterialEvolution_zero (y : ConcreteAnalysisSpace) :
    greenParsevalMaterialEvolution 0 y = y := by
  apply greenParsevalOrthogonalDecomposition.injective
  rw [evolution_decomposition]
  rw [productMaterialEvolution_apply, parsevalRangeMaterialEvolution_zero]

theorem greenParsevalMaterialEvolution_add (s r : ℝ) (y : ConcreteAnalysisSpace) :
    greenParsevalMaterialEvolution (s+r) y = greenParsevalMaterialEvolution s (greenParsevalMaterialEvolution r y) := by
  apply greenParsevalOrthogonalDecomposition.injective
  simp only [evolution_decomposition]
  simp only [productMaterialEvolution_apply, parsevalRangeMaterialEvolution_add]

theorem greenParsevalMaterialEvolution_neg (s : ℝ) :
    greenParsevalMaterialEvolution (-s) = (greenParsevalMaterialEvolution s).symm := by
  ext1 y
  apply (greenParsevalMaterialEvolution s).injective
  rw [← greenParsevalMaterialEvolution_add]
  simp

/-- Full-Hilbert intertwining: no unbounded-operator domain hypothesis. -/
theorem greenParsevalMaterialEvolution_intertwining (s : ℝ) (x : State) :
    greenParsevalMaterialEvolution s (greenParsevalAnalysis x) =
      greenParsevalAnalysis (greenStateMaterialEvolution s x) := by
  have hp : parsevalRangeSubmodule.orthogonalProjectionOnto (greenParsevalAnalysis x) = parsevalRangeUnitary x :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (parsevalRangeUnitary x)
  have hz : parsevalRangeSubmoduleᗮ.orthogonalProjectionOnto (greenParsevalAnalysis x) = 0 :=
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
      (parsevalRangeSubmodule.le_orthogonal_orthogonal (parsevalRangeUnitary x).property)
  rw [greenParsevalMaterialEvolution_apply, hp, hz]
  simp

theorem greenParsevalMaterialEvolution_eq_self_of_mem_orthogonal (s : ℝ)
    (y : ConcreteAnalysisSpace) (hy : y ∈ parsevalRangeSubmoduleᗮ) :
    greenParsevalMaterialEvolution s y = y := by
  have hz := Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hy
  have hp : (parsevalRangeSubmoduleᗮ.orthogonalProjectionOnto y : ConcreteAnalysisSpace) = y := by
    exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (⟨y,hy⟩ : ParsevalOrthogonal))
  rw [greenParsevalMaterialEvolution_apply, hz, map_zero, Submodule.coe_zero, zero_add, hp]

theorem greenParsevalMaterialEvolution_stronglyContinuous (y : ConcreteAnalysisSpace) :
    Continuous (fun s : ℝ => greenParsevalMaterialEvolution s y) := by
  have h : Continuous (fun s : ℝ => greenParsevalAnalysis
      (greenStateMaterialEvolution s (greenParsevalAnalysis.adjoint y)) +
      (parsevalRangeSubmoduleᗮ.orthogonalProjectionOnto y : ConcreteAnalysisSpace)) :=
    (greenParsevalAnalysis.continuous.comp
      (greenStateMaterialEvolution_stronglyContinuous (greenParsevalAnalysis.adjoint y))).add continuous_const
  simpa only [greenParsevalMaterialEvolution_apply_adjoint] using h

/-- The ambient strong derivative is transported, without coordinate calculation on Green channels. -/
theorem greenParsevalMaterialEvolution_hasDerivative_zero (y : ConcreteAnalysisSpace)
    (hy : y ∈ greenParsevalMaterialLogOperator.domain) :
    HasDerivAt (fun s : ℝ => greenParsevalMaterialEvolution s y)
      ((-Complex.I) • greenParsevalMaterialLogOperator ⟨y,hy⟩) 0 := by
  let r : ParsevalRange := parsevalRangeSubmodule.orthogonalProjectionOnto y
  let x : State := parsevalRangeUnitary.symm r
  have hr : r ∈ parsevalRangeMaterialLogGenerator.domain :=
    (greenParsevalMaterialLogOperator_domain_iff y).mp hy
  have hx : x ∈ greenStateMaterialLogGenerator.domain :=
    (parsevalRangeMaterialLogGenerator_domain_iff r).mp hr
  let B : State →L[ℂ] ConcreteAnalysisSpace :=
    parsevalRangeSubmodule.subtypeL.comp parsevalRangeUnitary.toContinuousLinearEquiv.toContinuousLinearMap
  have hv : greenParsevalMaterialLogOperator ⟨y,hy⟩ = B (greenStateMaterialLogGenerator ⟨x,hx⟩) := by
    change selfAdjointZeroExtension parsevalRangeSubmodule parsevalRangeMaterialLogGenerator ⟨y,hy⟩ = _
    rw [selfAdjointZeroExtension_apply]
    change (parsevalRangeUnitary (greenStateMaterialLogGenerator ⟨x,hx⟩) : ConcreteAnalysisSpace) = _
    rfl
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, greenParsevalMaterialEvolution_zero]
  have hm := (greenStateMaterialEvolution_hasDerivative_zero x hx).tendsto_slope_zero
  simp only [zero_add, greenStateMaterialEvolution_zero] at hm
  have ht := B.continuous.continuousAt.tendsto.comp hm
  have hsplit : y = B x + (parsevalRangeSubmoduleᗮ.orthogonalProjectionOnto y : ConcreteAnalysisSpace) := by
    have h0 := greenParsevalMaterialEvolution_apply 0 y
    change y = (parsevalRangeUnitary x : ConcreteAnalysisSpace) +
      (parsevalRangeSubmoduleᗮ.orthogonalProjectionOnto y : ConcreteAnalysisSpace)
    simpa only [greenParsevalMaterialEvolution_zero, parsevalRangeMaterialEvolution_apply,
      greenStateMaterialEvolution_zero, x, r] using h0
  have haction (s : ℝ) : greenParsevalMaterialEvolution s y =
      B (greenStateMaterialEvolution s x) + (parsevalRangeSubmoduleᗮ.orthogonalProjectionOnto y : ConcreteAnalysisSpace) := by
    exact greenParsevalMaterialEvolution_apply s y
  have hslope : (fun h : ℝ => h⁻¹ • (greenParsevalMaterialEvolution h y - y)) =
      (fun h : ℝ => B (h⁻¹ • (greenStateMaterialEvolution h x - x))) := by
    funext h
    have hdiff : greenParsevalMaterialEvolution h y - y = B (greenStateMaterialEvolution h x - x) := by
      calc
        _ = (B (greenStateMaterialEvolution h x) + (parsevalRangeSubmoduleᗮ.orthogonalProjectionOnto y : ConcreteAnalysisSpace)) -
            (B x + (parsevalRangeSubmoduleᗮ.orthogonalProjectionOnto y : ConcreteAnalysisSpace)) :=
          congrArg₂ (fun a b : ConcreteAnalysisSpace => a - b) (haction h) hsplit
        _ = _ := by rw [add_sub_add_right_eq_sub, map_sub]
    rw [hdiff]
    exact ((B.restrictScalars ℝ).map_smul h⁻¹ (greenStateMaterialEvolution h x - x)).symm
  rw [hslope, hv]
  simpa only [Function.comp_def, map_smul] using ht

/-- Agreement with the previous typed HP=PL theorem. -/
theorem greenParsevalMaterialEvolution_derivative_on_range (x : State)
    (hx : x ∈ greenStateMaterialLogGenerator.domain) :
    HasDerivAt (fun s : ℝ => greenParsevalMaterialEvolution s (greenParsevalAnalysis x))
      ((-Complex.I) • greenParsevalAnalysis (greenStateMaterialLogGenerator ⟨x,hx⟩)) 0 := by
  have hd := greenParsevalMaterialEvolution_hasDerivative_zero (greenParsevalAnalysis x)
    ((greenParsevalMaterialLogOperator_P_mem_domain_iff x).mpr hx)
  rw [greenParsevalMaterialLogOperator_intertwining x hx] at hd
  exact hd

/-- Every C2 CoreState has bounded evolution, regardless of its logarithmic moment. -/
theorem greenParsevalMaterialEvolution_c2Source (s t : ℝ) (V : CoreState) :
    greenParsevalMaterialEvolution s (greenParsevalAnalysis (c2GlobalGreenInputIsometry t V)) =
      greenParsevalAnalysis (greenStateMaterialEvolution s (c2GlobalGreenInputIsometry t V)) :=
  greenParsevalMaterialEvolution_intertwining s _

theorem greenParsevalMaterialEvolution_c2Source_add (s t : ℝ) (V : CoreState) :
    greenParsevalMaterialEvolution s (greenParsevalAnalysis (c2GlobalGreenInputIsometry t V)) =
      greenParsevalAnalysis (c2GlobalGreenInputIsometry (t+s) V) := by
  rw [greenParsevalMaterialEvolution_c2Source, c2GlobalGreenInput_evolution_add]

end GeometryOfNumbers.Analysis.GreenParsevalMaterialDynamics
