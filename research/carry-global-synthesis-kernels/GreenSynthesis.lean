import GeometryOfNumbers.Analysis.GreenParsevalMaterialLogOperator

/-! Two different kernels in the EXISTING Green/Parseval construction.
The frame-null component is coefficient redundancy. The physical escape
from a selected C2 branch is retained separately, with its real polarization.
No operator, source, or metric is constructed from canonical moments. -/
namespace CarryGlobalGreenSynthesis
open GeometryOfNumbers.Analysis GreenFrame.Concrete
open GeometryOfNumbers.Analysis.C2GlobalGreenBridge
open GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy
open GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
open GeometryOfNumbers.Analysis.GreenStateMaterialLog
open scoped InnerProductSpace BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Only real scalar packaging of the already defined canonical Parseval map. -/
def originalParseval : State →ₗᵢ[ℝ] ConcreteAnalysisSpace :=
  { greenParsevalAnalysis.restrictScalars ℝ with
    norm_map' := canonicalGreenAnalysis_norm }

/-- The adjoint of that same map; no new dynamics or inverse is chosen. -/
abbrev sourceSynthesis : ConcreteAnalysisSpace →L[ℝ] State :=
  originalParseval.toContinuousLinearMap.adjoint

def frameNull (z : ConcreteAnalysisSpace) : ConcreteAnalysisSpace :=
  z-originalParseval (sourceSynthesis z)

def branchState (t : ℝ) (z : ConcreteAnalysisSpace) : CoreState :=
  (c2GlobalGreenInputIsometry t).toContinuousLinearMap.adjoint (sourceSynthesis z)

def physicalEscape (t : ℝ) (z : ConcreteAnalysisSpace) : State :=
  sourceSynthesis z-c2GlobalGreenInputIsometry t (branchState t z)

theorem synthesis_parseval (x : State) : sourceSynthesis (originalParseval x) = x := by
  exact congrArg (fun T : State →L[ℝ] State => T x) originalParseval.adjoint_comp_self

theorem synthesis_frame_null (z : ConcreteAnalysisSpace) : sourceSynthesis (frameNull z) = 0 := by
  rw [frameNull,map_sub,synthesis_parseval,sub_self]

theorem frame_null_parseval (x : State) : frameNull (originalParseval x) = 0 := by
  rw [frameNull,synthesis_parseval,sub_self]

theorem coefficient_kernel_exact (z : ConcreteAnalysisSpace) :
    sourceSynthesis z = 0 ↔ frameNull z = z := by
  constructor
  · intro h
    simp only [frameNull,h,map_zero,sub_zero]
  · intro h
    have he := congrArg sourceSynthesis h
    rw [synthesis_frame_null] at he
    exact he.symm

theorem same_physical_state_iff (z w : ConcreteAnalysisSpace) :
    sourceSynthesis z = sourceSynthesis w ↔ sourceSynthesis (z-w) = 0 := by
  rw [map_sub,sub_eq_zero]

private theorem isometry_pairing_split
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (U : E →ₗᵢ[ℝ] F) (z w : F) :
    inner ℝ z w = inner ℝ (U.toContinuousLinearMap.adjoint z) (U.toContinuousLinearMap.adjoint w) +
      inner ℝ (z-U (U.toContinuousLinearMap.adjoint z)) (w-U (U.toContinuousLinearMap.adjoint w)) := by
  rw [inner_sub_left,inner_sub_right,inner_sub_right,U.inner_map_map]
  have hl : inner ℝ (U (U.toContinuousLinearMap.adjoint z)) w =
      inner ℝ (U.toContinuousLinearMap.adjoint z) (U.toContinuousLinearMap.adjoint w) :=
    (U.toContinuousLinearMap.adjoint_inner_right _ _).symm
  have hr : inner ℝ z (U (U.toContinuousLinearMap.adjoint w)) =
      inner ℝ (U.toContinuousLinearMap.adjoint z) (U.toContinuousLinearMap.adjoint w) :=
    (U.toContinuousLinearMap.adjoint_inner_left _ _).symm
  rw [hl,hr]
  ring

/-- The true coefficient quotient preserves ALL material states and all crosses. -/
theorem frame_polarized_split (z w : ConcreteAnalysisSpace) :
    inner ℝ z w = inner ℝ (sourceSynthesis z) (sourceSynthesis w) +
      inner ℝ (frameNull z) (frameNull w) :=
  isometry_pairing_split originalParseval z w

/-- Orthogonal branch escape is not silently identified with coefficient redundancy. -/
theorem complete_polarized_split (t : ℝ) (z w : ConcreteAnalysisSpace) :
    inner ℝ z w = inner ℝ (branchState t z) (branchState t w) +
      inner ℝ (physicalEscape t z) (physicalEscape t w) +
      inner ℝ (frameNull z) (frameNull w) := by
  rw [frame_polarized_split]
  have h := isometry_pairing_split (c2GlobalGreenInputIsometry t)
    (sourceSynthesis z) (sourceSynthesis w)
  change inner ℝ (sourceSynthesis z) (sourceSynthesis w) =
    inner ℝ (branchState t z) (branchState t w) +
      inner ℝ (physicalEscape t z) (physicalEscape t w) at h
  rw [h]

theorem complete_energy_split (t : ℝ) (z : ConcreteAnalysisSpace) :
    ‖z‖^2 = ‖branchState t z‖^2+‖physicalEscape t z‖^2+‖frameNull z‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using complete_polarized_split t z z

theorem physical_quotient_energy (t : ℝ) (z : ConcreteAnalysisSpace) :
    ‖sourceSynthesis z‖^2 = ‖branchState t z‖^2+‖physicalEscape t z‖^2 := by
  simpa only [real_inner_self_eq_norm_sq,branchState,physicalEscape] using
    isometry_pairing_split (c2GlobalGreenInputIsometry t) (sourceSynthesis z) (sourceSynthesis z)

theorem branch_choice_preserves_total (t u : ℝ) (z : ConcreteAnalysisSpace) :
    ‖branchState t z‖^2+‖physicalEscape t z‖^2 =
      ‖branchState u z‖^2+‖physicalEscape u z‖^2 := by
  rw [← physical_quotient_energy, ← physical_quotient_energy]

theorem quotient_energy_minimum (z w : ConcreteAnalysisSpace)
    (h : sourceSynthesis w = sourceSynthesis z) :
    ‖originalParseval (sourceSynthesis z)‖^2 ≤ ‖w‖^2 := by
  have he := frame_polarized_split w w
  simp only [real_inner_self_eq_norm_sq] at he
  rw [originalParseval.norm_map, ← h]
  nlinarith [sq_nonneg ‖frameNull w‖]

/-- Existing physical clock domains survive on the canonical representative. -/
theorem reconstructed_domain_iff (z : ConcreteAnalysisSpace) :
    greenParsevalAnalysis (sourceSynthesis z) ∈ greenParsevalMaterialLogOperator.domain ↔
      sourceSynthesis z ∈ greenStateMaterialLogGenerator.domain :=
  greenParsevalMaterialLogOperator_P_mem_domain_iff _

theorem reconstructed_clock_intertwines (z : ConcreteAnalysisSpace)
    (hz : sourceSynthesis z ∈ greenStateMaterialLogGenerator.domain) :
    greenParsevalMaterialLogOperator
      ⟨greenParsevalAnalysis (sourceSynthesis z),
        (reconstructed_domain_iff z).mpr hz⟩ =
      greenParsevalAnalysis (greenStateMaterialLogGenerator ⟨sourceSynthesis z,hz⟩) :=
  greenParsevalMaterialLogOperator_intertwining _ hz

private theorem real_inner_complex_re {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [InnerProductSpace ℝ H] (x y : H) :
    inner ℝ x y = (inner ℂ x y).re := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two]
  exact (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) x y).symm

theorem synthesis_real_complex_compatible :
    sourceSynthesis = greenParsevalAnalysis.adjoint.restrictScalars ℝ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ originalParseval.toContinuousLinearMap).mpr
  intro z x
  change inner ℝ (greenParsevalAnalysis.adjoint z) x = inner ℝ z (greenParsevalAnalysis x)
  rw [real_inner_complex_re,real_inner_complex_re]
  exact congrArg Complex.re (greenParsevalAnalysis.adjoint_inner_left x z)

/-- Canonical frame normalization has exactly the OLD coefficient-null
directions. No independent material direction is relabeled as redundant. -/
theorem raw_canonical_same_coefficient_kernel (z : ConcreteAnalysisSpace) :
    sourceSynthesis z = 0 ↔ canonicalRawGreenAnalysis.adjoint z = 0 := by
  rw [synthesis_real_complex_compatible]
  change (canonicalAnalysis canonicalRawGreenAnalysis).adjoint z = 0 ↔ _
  rw [canonicalAnalysis,ContinuousLinearMap.adjoint_comp,inverseSqrtFrame_adjoint]
  change inverseSqrtFrame canonicalRawGreenAnalysis (canonicalRawGreenAnalysis.adjoint z) = 0 ↔ _
  constructor
  · intro h
    have hi := congrArg (fun T : State →L[ℂ] State => T (canonicalRawGreenAnalysis.adjoint z))
      canonicalRawGreen_inverseSqrt_normalization
    change inverseSqrtFrame canonicalRawGreenAnalysis
      (frameOperator canonicalRawGreenAnalysis
        (inverseSqrtFrame canonicalRawGreenAnalysis (canonicalRawGreenAnalysis.adjoint z))) =
      canonicalRawGreenAnalysis.adjoint z at hi
    rw [h,map_zero,map_zero] at hi
    exact hi.symm
  · intro h
    rw [h,map_zero]

theorem synthesis_homogeneous_energy (beta : ℝ) (z : ConcreteAnalysisSpace) :
    ‖sourceSynthesis (beta • z)‖^2 = beta^2*‖sourceSynthesis z‖^2 := by
  rw [map_smul,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

/-- An original material state, outside every C2 source range, is NOT frame-null. -/
theorem c2_seed_compression_zero (t : ℝ) :
    (c2GlobalGreenInputIsometry t).toContinuousLinearMap.adjoint (greenMaterialBasisVector 1) = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [(c2GlobalGreenInputIsometry t).toContinuousLinearMap.adjoint_inner_left,
    real_inner_complex_re]
  simp only [greenMaterialBasisVector,lp.inner_single_left]
  change (inner ℂ (1 : ℂ) ((c2GlobalGreenInputIsometry t) _ 1)).re = 0
  rw [c2GlobalGreenInput_one]
  simp

theorem physical_seed_not_redundant (t : ℝ) :
    let z := originalParseval (greenMaterialBasisVector 1)
    frameNull z = 0 ∧ branchState t z = 0 ∧
      physicalEscape t z = greenMaterialBasisVector 1 ∧ ‖z‖^2 = 1 := by
  dsimp only
  refine ⟨frame_null_parseval _,?_,?_,?_⟩
  · rw [branchState,synthesis_parseval,c2_seed_compression_zero]
  · rw [physicalEscape,branchState,synthesis_parseval,c2_seed_compression_zero,map_zero,sub_zero]
  · rw [originalParseval.norm_map,greenMaterialBasisVector,lp.norm_single (by norm_num)]
    norm_num

end
end CarryGlobalGreenSynthesis
