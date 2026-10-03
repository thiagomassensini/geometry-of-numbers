import GeometryOfNumbers.Analysis.GreenStateMaterialLogGenerator
import Batteries.Tactic.OpenPrivate

/-!
# Ambient Green material clock through the canonical Parseval range

The operator is the transported material logarithmic clock on the closed
Parseval range, and zero on its canonical orthogonal complement.
The C2 logarithmic domain moment remains a separate gate.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProduct Topology lp
open private unitaryTransport unitaryTransport_apply unitaryTransport_dense
  unitaryTransport_isSelfAdjoint from GeometryOfNumbers.Analysis.GreenStateMaterialLogGenerator

namespace GeometryOfNumbers.Analysis.UnitaryZeroExtension

variable {R S K : Type} [NormedAddCommGroup R] [InnerProductSpace ℂ R]
  [NormedAddCommGroup S] [InnerProductSpace ℂ S]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- A ⊕ 0 on the genuine L² product, with domain Dom(A) × S. -/
def hilbertPartialProdZero (A : R →ₗ.[ℂ] R) :
    WithLp 2 (R × S) →ₗ.[ℂ] WithLp 2 (R × S) where
  domain := A.domain.comap (WithLp.fstL 2 ℂ R S).toLinearMap
  toFun := (WithLp.linearEquiv 2 ℂ (R × S)).symm.toLinearMap.comp
    ((A.toFun.comp (((WithLp.fstL 2 ℂ R S).toLinearMap.domRestrict _).codRestrict _
      (fun x => x.prop))).prod 0)

theorem hilbertPartialProdZero_mem_domain_iff (A : R →ₗ.[ℂ] R)
    (y : WithLp 2 (R × S)) :
    y ∈ (hilbertPartialProdZero (S := S) A).domain ↔ (WithLp.ofLp y).1 ∈ A.domain := Iff.rfl

theorem hilbertPartialProdZero_apply (A : R →ₗ.[ℂ] R)
    (y : (hilbertPartialProdZero (S := S) A).domain) :
    hilbertPartialProdZero A y = WithLp.toLp 2 (A ⟨(WithLp.ofLp y.val).1,y.prop⟩,0) := rfl

theorem hilbertPartialProdZero_dense_domain (A : R →ₗ.[ℂ] R)
    (hA : Dense (A.domain : Set R)) :
    Dense ((hilbertPartialProdZero (S := S) A).domain : Set (WithLp 2 (R × S))) := by
  have h := (hA.prod (dense_univ : Dense (Set.univ : Set S))).preimage
    (WithLp.prodContinuousLinearEquiv 2 ℂ R S).toHomeomorph.isOpenMap
  convert h using 1
  ext y
  simp [hilbertPartialProdZero]

/-- Maximality of the adjoint is inherited independently in the A and zero slots. -/
theorem hilbertPartialProdZero_isSelfAdjoint [CompleteSpace R] [CompleteSpace S]
    (A : R →ₗ.[ℂ] R) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (hilbertPartialProdZero (S := S) A) := by
  let B := hilbertPartialProdZero (S := S) A
  have hAd := hA.dense_domain
  have hBd : Dense (B.domain : Set (WithLp 2 (R × S))) :=
    hilbertPartialProdZero_dense_domain A hAd
  have hEq : A.adjoint = A := LinearPMap.isSelfAdjoint_def.mp hA
  have hAf : A.IsFormalAdjoint A := by
    simpa only [hEq] using (LinearPMap.adjoint_isFormalAdjoint hAd (T := A))
  have hBf : B.IsFormalAdjoint B := by
    intro x y
    have h := hAf ⟨(WithLp.ofLp x.val).1,x.prop⟩ ⟨(WithLp.ofLp y.val).1,y.prop⟩
    simpa only [B, hilbertPartialProdZero_apply, WithLp.prod_inner_apply,
      WithLp.ofLp_toLp, inner_zero_left, inner_zero_right, add_zero] using h
  have hDom : B.adjoint.domain ≤ B.domain := by
    intro y hy
    let yB : B.adjoint.domain := ⟨y,hy⟩
    have hNative : (WithLp.ofLp y).1 ∈ A.adjoint.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨(WithLp.ofLp (B.adjoint yB)).1, ?_⟩
      intro x
      let xB : B.domain := ⟨WithLp.toLp 2 (x.val,0),x.prop⟩
      have h := (LinearPMap.adjoint_isFormalAdjoint hBd (T := B)) yB xB
      have he : B xB = WithLp.toLp 2 (A x,0) := rfl
      rw [he] at h
      simpa only [xB, WithLp.prod_inner_apply, WithLp.ofLp_toLp,
        inner_zero_right, add_zero] using h
    change (WithLp.ofLp y).1 ∈ A.domain
    simpa only [hEq] using hNative
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨hDom, ?_⟩
    intro x y hxy
    apply hBd.eq_of_inner_left ℂ
    intro z hz
    have hx := (LinearPMap.adjoint_isFormalAdjoint hBd (T := B)) x ⟨z,hz⟩
    have hy := hBf y ⟨z,hz⟩
    exact hx.trans (by rw [hxy]; exact hy.symm)
  · exact hBf.le_adjoint hBd

/-- Canonical orthogonal extension, using no arbitrary complement. -/
def selfAdjointZeroExtension (Q : Submodule ℂ K) [Q.HasOrthogonalProjection]
    (A : Q →ₗ.[ℂ] Q) : K →ₗ.[ℂ] K :=
  unitaryTransport Q.orthogonalDecomposition.symm (hilbertPartialProdZero (S := Qᗮ) A)

theorem selfAdjointZeroExtension_domain_iff (Q : Submodule ℂ K) [Q.HasOrthogonalProjection]
    (A : Q →ₗ.[ℂ] Q) (y : K) :
    y ∈ (selfAdjointZeroExtension Q A).domain ↔ Q.orthogonalProjectionOnto y ∈ A.domain := by
  change (WithLp.ofLp (Q.orthogonalDecomposition y)).1 ∈ A.domain ↔ _
  rw [Submodule.orthogonalDecomposition_apply]

theorem selfAdjointZeroExtension_apply (Q : Submodule ℂ K) [Q.HasOrthogonalProjection]
    (A : Q →ₗ.[ℂ] Q) (y : (selfAdjointZeroExtension Q A).domain) :
    selfAdjointZeroExtension Q A y =
      (A ⟨Q.orthogonalProjectionOnto y.val,
        (selfAdjointZeroExtension_domain_iff Q A y.val).mp y.prop⟩ : K) := by
  change Q.orthogonalDecomposition.symm
    (WithLp.toLp 2 (A ⟨(WithLp.ofLp (Q.orthogonalDecomposition y.val)).1,_⟩,0)) = _
  simp [Submodule.orthogonalDecomposition_apply]

theorem selfAdjointZeroExtension_isSelfAdjoint [CompleteSpace K]
    (Q : Submodule ℂ K) [CompleteSpace Q] [CompleteSpace Qᗮ]
    (A : Q →ₗ.[ℂ] Q) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (selfAdjointZeroExtension Q A) :=
  unitaryTransport_isSelfAdjoint Q.orthogonalDecomposition.symm _
    (hilbertPartialProdZero_isSelfAdjoint A hA)

end GeometryOfNumbers.Analysis.UnitaryZeroExtension

namespace GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
open GreenFrame.Concrete GreenStateMaterialLog C2GreenWhiteningGenealogy
open GeometryOfNumbers.Analysis C2GlobalGreenBridge UnitaryZeroExtension

/-- Exactly the previous canonical analysis; no alternative isometry. -/
abbrev greenParsevalAnalysis : State →L[ℂ] ConcreteAnalysisSpace :=
  canonicalAnalysis canonicalRawGreenAnalysis

theorem greenParsevalAnalysis_gram_identity :
    greenParsevalAnalysis.adjoint.comp greenParsevalAnalysis = 1 := canonicalGreenAnalysis_gram_identity

theorem greenParsevalAnalysis_isometry : Isometry greenParsevalAnalysis := canonicalGreenAnalysis_isometry

def parsevalRangeSubmodule : Submodule ℂ ConcreteAnalysisSpace := greenParsevalAnalysis.toLinearMap.range
abbrev ParsevalRange : Type := ↥parsevalRangeSubmodule
abbrev ParsevalOrthogonal : Type := ↥parsevalRangeSubmoduleᗮ

theorem parsevalRange_isClosed : IsClosed (parsevalRangeSubmodule : Set ConcreteAnalysisSpace) :=
  greenParsevalAnalysis_isometry.isClosedEmbedding.isClosed_range

instance parsevalRange_completeSpace : CompleteSpace ParsevalRange :=
  parsevalRange_isClosed.isComplete.completeSpace_coe

/-- Bundling the same canonical P onto its range. -/
def parsevalRangeUnitary : State ≃ₗᵢ[ℂ] ParsevalRange :=
  (canonicalParseval canonicalRawGreenFrameBounds).equivRange

@[simp] theorem parsevalRangeUnitary_apply (x : State) :
    (parsevalRangeUnitary x : ConcreteAnalysisSpace) = greenParsevalAnalysis x := rfl

def parsevalRangeMaterialLogGenerator :=
  unitaryTransport (H := State) (K := ParsevalRange) parsevalRangeUnitary greenStateMaterialLogGenerator

theorem parsevalRangeMaterialLogGenerator_domain_iff (y : ParsevalRange) :
    y ∈ parsevalRangeMaterialLogGenerator.domain ↔
    parsevalRangeUnitary.symm y ∈ greenStateMaterialLogGenerator.domain := Iff.rfl

set_option linter.defProp false in
/-- Named proof from the previous transport theorem; inference retains its exact Hilbert instances. -/
def parsevalRangeMaterialLogGenerator_isSelfAdjoint :=
  unitaryTransport_isSelfAdjoint (H := State) (K := ParsevalRange)
    parsevalRangeUnitary greenStateMaterialLogGenerator greenStateMaterialLogGenerator_isSelfAdjoint

theorem parsevalRangeMaterialLogGenerator_unitary_mem_domain_iff (x : State) :
    parsevalRangeUnitary x ∈ parsevalRangeMaterialLogGenerator.domain ↔
    x ∈ greenStateMaterialLogGenerator.domain := by
  rw [parsevalRangeMaterialLogGenerator_domain_iff, parsevalRangeUnitary.symm_apply_apply]

theorem parsevalRangeMaterialLogGenerator_intertwines (x : State)
    (hx : x ∈ greenStateMaterialLogGenerator.domain) :
    parsevalRangeMaterialLogGenerator
      ⟨parsevalRangeUnitary x,(parsevalRangeMaterialLogGenerator_unitary_mem_domain_iff x).mpr hx⟩ =
      parsevalRangeUnitary (greenStateMaterialLogGenerator ⟨x,hx⟩) := by
  change parsevalRangeUnitary (greenStateMaterialLogGenerator ⟨parsevalRangeUnitary.symm (parsevalRangeUnitary x),_⟩) = _
  congr 2
  apply Subtype.ext
  simp

/-- Canonical closed-range/orthogonal decomposition of the ambient analysis carrier. -/
def greenParsevalOrthogonalDecomposition :
    ConcreteAnalysisSpace ≃ₗᵢ[ℂ] WithLp 2 (ParsevalRange × ParsevalOrthogonal) :=
  parsevalRangeSubmodule.orthogonalDecomposition

/-- The range clock ⊕ zero, literally in the ambient Green analysis space. -/
def greenParsevalMaterialLogOperator : ConcreteAnalysisSpace →ₗ.[ℂ] ConcreteAnalysisSpace :=
  selfAdjointZeroExtension parsevalRangeSubmodule parsevalRangeMaterialLogGenerator

theorem greenParsevalMaterialLogOperator_isSelfAdjoint :
    IsSelfAdjoint greenParsevalMaterialLogOperator :=
  selfAdjointZeroExtension_isSelfAdjoint _ _ parsevalRangeMaterialLogGenerator_isSelfAdjoint


theorem greenParsevalMaterialLogOperator_domain_iff (y : ConcreteAnalysisSpace) :
    y ∈ greenParsevalMaterialLogOperator.domain ↔
    parsevalRangeSubmodule.orthogonalProjectionOnto y ∈ parsevalRangeMaterialLogGenerator.domain :=
  selfAdjointZeroExtension_domain_iff _ _ y

theorem greenParsevalMaterialLogOperator_P_mem_domain_iff (x : State) :
    greenParsevalAnalysis x ∈ greenParsevalMaterialLogOperator.domain ↔
    x ∈ greenStateMaterialLogGenerator.domain := by
  rw [greenParsevalMaterialLogOperator_domain_iff]
  change parsevalRangeSubmodule.orthogonalProjectionOnto
    (parsevalRangeUnitary x : ConcreteAnalysisSpace) ∈ parsevalRangeMaterialLogGenerator.domain ↔ _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  exact parsevalRangeMaterialLogGenerator_unitary_mem_domain_iff x

theorem greenParsevalMaterialLogOperator_intertwining (x : State)
    (hx : x ∈ greenStateMaterialLogGenerator.domain) :
    greenParsevalMaterialLogOperator
      ⟨greenParsevalAnalysis x,(greenParsevalMaterialLogOperator_P_mem_domain_iff x).mpr hx⟩ =
      greenParsevalAnalysis (greenStateMaterialLogGenerator ⟨x,hx⟩) := by
  let hPx := (greenParsevalMaterialLogOperator_P_mem_domain_iff x).mpr hx
  have hp : parsevalRangeSubmodule.orthogonalProjectionOnto (greenParsevalAnalysis x) =
      parsevalRangeUnitary x :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (parsevalRangeUnitary x)
  have hProj := (greenParsevalMaterialLogOperator_domain_iff (greenParsevalAnalysis x)).mp hPx
  have he : (⟨parsevalRangeSubmodule.orthogonalProjectionOnto (greenParsevalAnalysis x),hProj⟩ :
      parsevalRangeMaterialLogGenerator.domain) =
      ⟨parsevalRangeUnitary x,(parsevalRangeMaterialLogGenerator_unitary_mem_domain_iff x).mpr hx⟩ :=
    Subtype.ext hp
  change selfAdjointZeroExtension parsevalRangeSubmodule parsevalRangeMaterialLogGenerator
    ⟨greenParsevalAnalysis x,hPx⟩ = _
  rw [selfAdjointZeroExtension_apply, he, parsevalRangeMaterialLogGenerator_intertwines,
    parsevalRangeUnitary_apply]

theorem greenParsevalMaterialLogOperator_mem_domain_of_mem_orthogonal
    (y : ConcreteAnalysisSpace) (hy : y ∈ parsevalRangeSubmoduleᗮ) :
    y ∈ greenParsevalMaterialLogOperator.domain := by
  rw [greenParsevalMaterialLogOperator_domain_iff,
    Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hy]
  exact Submodule.zero_mem _

theorem greenParsevalMaterialLogOperator_eq_zero_of_mem_orthogonal
    (y : ConcreteAnalysisSpace) (hy : y ∈ parsevalRangeSubmoduleᗮ) :
    greenParsevalMaterialLogOperator
      ⟨y,greenParsevalMaterialLogOperator_mem_domain_of_mem_orthogonal y hy⟩ = 0 := by
  let hY := greenParsevalMaterialLogOperator_mem_domain_of_mem_orthogonal y hy
  have hProj := (greenParsevalMaterialLogOperator_domain_iff y).mp hY
  have he : (⟨parsevalRangeSubmodule.orthogonalProjectionOnto y,hProj⟩ :
      parsevalRangeMaterialLogGenerator.domain) = 0 :=
    Subtype.ext (Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hy)
  change selfAdjointZeroExtension parsevalRangeSubmodule parsevalRangeMaterialLogGenerator ⟨y,hY⟩ = 0
  rw [selfAdjointZeroExtension_apply, he, LinearPMap.map_zero]
  rfl

theorem greenParsevalMaterialLogOperator_transported_basis (n : PNat) :
    greenParsevalMaterialLogOperator
      ⟨greenParsevalAnalysis (greenMaterialBasisVector n),
        (greenParsevalMaterialLogOperator_P_mem_domain_iff _).mpr (greenMaterialBasisVector_mem_domain n)⟩ =
      (Real.log (n : ℝ) : ℂ) • greenParsevalAnalysis (greenMaterialBasisVector n) := by
  rw [greenParsevalMaterialLogOperator_intertwining _ (greenMaterialBasisVector_mem_domain n),
    greenStateMaterialLogGenerator_basisVector_log, map_smul]

theorem greenParsevalMaterialLogOperator_transported_basis_ne_zero (n : PNat) :
    greenParsevalAnalysis (greenMaterialBasisVector n) ≠ 0 := by
  intro hz
  have hn : greenMaterialBasisVector n = 0 := greenParsevalAnalysis_isometry.injective (by simpa using hz)
  have h := congrArg (fun f : State => f n) hn
  simp [greenMaterialBasisVector] at h

/-- Conditional: no assertion that every C2 CoreState has the logarithmic moment. -/
theorem greenParsevalMaterialLogOperator_c2Source_mem_domain (t : ℝ) (V : CoreState)
    (hx : c2GlobalGreenInputIsometry t V ∈ greenStateMaterialLogGenerator.domain) :
    greenParsevalAnalysis (c2GlobalGreenInputIsometry t V) ∈ greenParsevalMaterialLogOperator.domain :=
  (greenParsevalMaterialLogOperator_P_mem_domain_iff _).mpr hx

theorem greenParsevalMaterialLogOperator_c2Source_intertwining (t : ℝ) (V : CoreState)
    (hx : c2GlobalGreenInputIsometry t V ∈ greenStateMaterialLogGenerator.domain) :
    greenParsevalMaterialLogOperator
      ⟨greenParsevalAnalysis (c2GlobalGreenInputIsometry t V),
        greenParsevalMaterialLogOperator_c2Source_mem_domain t V hx⟩ =
      greenParsevalAnalysis (greenStateMaterialLogGenerator ⟨c2GlobalGreenInputIsometry t V,hx⟩) :=
  greenParsevalMaterialLogOperator_intertwining _ hx

theorem greenParsevalMaterialLogOperator_c2Source_domain_iff_log_moment (t : ℝ) (V : CoreState) :
    greenParsevalAnalysis (c2GlobalGreenInputIsometry t V) ∈ greenParsevalMaterialLogOperator.domain ↔
    Summable (fun n : PNat => (Real.log (n : ℝ))^2 *
      Complex.normSq (c2GlobalGreenInputIsometry 0 V n)) := by
  rw [greenParsevalMaterialLogOperator_P_mem_domain_iff, c2Source_log_domain_iff]

end GeometryOfNumbers.Analysis.GreenParsevalMaterialLog
