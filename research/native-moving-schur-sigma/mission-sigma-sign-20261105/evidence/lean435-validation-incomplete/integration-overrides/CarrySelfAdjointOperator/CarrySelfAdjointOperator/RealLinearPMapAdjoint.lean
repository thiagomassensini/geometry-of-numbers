import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-!
# Maximal adjoints for real partial linear maps

`Mathlib.Analysis.InnerProductSpace.LinearPMap` supplies the standard adjoint
over an abstract `RCLike` scalar.  The concrete real operator tower in this
project is elaborated with the canonical `Real.instRing`, whereas the generic
API currently projects a second ring instance through `RCLike`.  This file
states the same maximal construction directly over the canonical real scalar.

The domain consists exactly of those vectors whose adjoint functional is
represented by an ambient vector.  Density of the original domain makes that
representative unique.  No boundedness or extension choice is introduced.
-/

open scoped InnerProductSpace RealInnerProductSpace

namespace LinearPMap

noncomputable section

variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- Domain of the maximal real adjoint.  A vector belongs to the domain
exactly when its adjoint functional is represented by a vector in the source
Hilbert space. -/
def realAdjointDomain (T : E →ₗ.[ℝ] F) : Submodule ℝ F where
  carrier := {y | ∃ w : E, ∀ x : T.domain,
    ⟪w, (x : E)⟫_ℝ = ⟪y, T x⟫_ℝ}
  zero_mem' := by
    refine ⟨0, fun x => ?_⟩
    simp
  add_mem' := by
    rintro y z ⟨wy, hwy⟩ ⟨wz, hwz⟩
    refine ⟨wy + wz, fun x => ?_⟩
    rw [inner_add_left, inner_add_left, hwy x, hwz x]
  smul_mem' := by
    rintro c y ⟨w, hw⟩
    refine ⟨c • w, fun x => ?_⟩
    rw [real_inner_smul_left, real_inner_smul_left, hw x]

/-- The chosen representing vector for an element of the maximal real
adjoint domain. -/
def realAdjointValue (T : E →ₗ.[ℝ] F) (y : T.realAdjointDomain) : E :=
  Classical.choose y.property

theorem realAdjointValue_inner (T : E →ₗ.[ℝ] F)
    (y : T.realAdjointDomain) (x : T.domain) :
    ⟪T.realAdjointValue y, (x : E)⟫_ℝ =
      ⟪(y : F), T x⟫_ℝ :=
  Classical.choose_spec y.property x

/-- The maximal adjoint of a densely defined real partial linear map. -/
def realAdjoint (T : E →ₗ.[ℝ] F)
    (hT : Dense (T.domain : Set E)) : F →ₗ.[ℝ] E where
  domain := T.realAdjointDomain
  toFun :=
    { toFun := T.realAdjointValue
      map_add' := fun y z => by
        apply hT.eq_of_inner_left ℝ
        intro x hx
        let xd : T.domain := ⟨x, hx⟩
        change
          ⟪T.realAdjointValue (y + z), (xd : E)⟫_ℝ =
            ⟪T.realAdjointValue y + T.realAdjointValue z, (xd : E)⟫_ℝ
        rw [inner_add_left,
          T.realAdjointValue_inner (y + z) xd,
          T.realAdjointValue_inner y xd,
          T.realAdjointValue_inner z xd]
        change
          ⟪(y : F) + (z : F), T xd⟫_ℝ =
            ⟪(y : F), T xd⟫_ℝ + ⟪(z : F), T xd⟫_ℝ
        exact inner_add_left _ _ _
      map_smul' := fun c y => by
        apply hT.eq_of_inner_left ℝ
        intro x hx
        let xd : T.domain := ⟨x, hx⟩
        change
          ⟪T.realAdjointValue (c • y), (xd : E)⟫_ℝ =
            ⟪c • T.realAdjointValue y, (xd : E)⟫_ℝ
        rw [real_inner_smul_left,
          T.realAdjointValue_inner (c • y) xd,
          T.realAdjointValue_inner y xd]
        change
          ⟪c • (y : F), T xd⟫_ℝ =
            c * ⟪(y : F), T xd⟫_ℝ
        exact real_inner_smul_left _ _ _ }

@[simp] theorem realAdjoint_domain (T : E →ₗ.[ℝ] F)
    (hT : Dense (T.domain : Set E)) :
    (T.realAdjoint hT).domain = T.realAdjointDomain :=
  rfl

/-- Fundamental representing identity for the maximal real adjoint. -/
theorem realAdjoint_inner (T : E →ₗ.[ℝ] F)
    (hT : Dense (T.domain : Set E))
    (y : (T.realAdjoint hT).domain) (x : T.domain) :
    ⟪T.realAdjoint hT y, (x : E)⟫_ℝ =
      ⟪(y : F), T x⟫_ℝ :=
  T.realAdjointValue_inner y x

/-- The maximal adjoint is a genuine formal adjoint in the usual orientation. -/
theorem realAdjoint_isFormalAdjoint (T : E →ₗ.[ℝ] F)
    (hT : Dense (T.domain : Set E)) :
    ∀ (x : T.domain) (y : (T.realAdjoint hT).domain),
      ⟪T x, (y : F)⟫_ℝ =
        ⟪(x : E), T.realAdjoint hT y⟫_ℝ := by
  intro x y
  calc
    ⟪T x, (y : F)⟫_ℝ = ⟪(y : F), T x⟫_ℝ := real_inner_comm _ _
    _ = ⟪T.realAdjoint hT y, (x : E)⟫_ℝ :=
      (T.realAdjoint_inner hT y x).symm
    _ = ⟪(x : E), T.realAdjoint hT y⟫_ℝ := real_inner_comm _ _

/-- The representing vector is unique on a dense domain. -/
theorem realAdjoint_apply_eq (T : E →ₗ.[ℝ] F)
    (hT : Dense (T.domain : Set E))
    (y : (T.realAdjoint hT).domain) {w : E}
    (hw : ∀ x : T.domain,
      ⟪w, (x : E)⟫_ℝ = ⟪(y : F), T x⟫_ℝ) :
    T.realAdjoint hT y = w := by
  apply hT.eq_of_inner_left ℝ
  intro x hx
  let xd : T.domain := ⟨x, hx⟩
  exact (T.realAdjoint_inner hT y xd).trans (hw xd).symm

/-- Every real formal adjoint is contained in the maximal real adjoint. -/
theorem le_realAdjoint_of_formalAdjoint
    (T : E →ₗ.[ℝ] F) (S : F →ₗ.[ℝ] E)
    (hT : Dense (T.domain : Set E))
    (hformal : ∀ (x : T.domain) (y : S.domain),
      ⟪T x, (y : F)⟫_ℝ = ⟪(x : E), S y⟫_ℝ) :
    S ≤ T.realAdjoint hT := by
  constructor
  · intro y hy
    change y ∈ T.realAdjointDomain
    refine ⟨S ⟨y, hy⟩, fun x => ?_⟩
    rw [real_inner_comm, ← hformal x ⟨y, hy⟩, real_inner_comm]
  · intro y z hyz
    symm
    apply T.realAdjoint_apply_eq hT z
    intro x
    rw [← hyz, real_inner_comm, ← hformal x y, real_inner_comm]

/-! ## Formal adjoints of algebraic inverses -/

/-- If two injective partial real-linear maps are formal adjoints, then their
algebraic inverses are formal adjoints on their natural range domains. -/
theorem inverse_formalAdjointIdentity
    (T : E →ₗ.[ℝ] F) (S : F →ₗ.[ℝ] E)
    (hTker : T.ker = ⊥)
    (hSker : S.ker = ⊥)
    (hformal : ∀ (x : T.domain) (y : S.domain),
      ⟪T x, (y : F)⟫_ℝ = ⟪(x : E), S y⟫_ℝ) :
    ∀ (x : T.inverse.domain) (y : S.inverse.domain),
      ⟪T.inverse x, (y : E)⟫_ℝ =
        ⟪(x : F), S.inverse y⟫_ℝ := by
  intro x y
  have hxrange : (x : F) ∈ LinearMap.range T.toFun := by
    simpa only [LinearPMap.inverse_domain] using x.property
  have hyrange : (y : E) ∈ LinearMap.range S.toFun := by
    simpa only [LinearPMap.inverse_domain] using y.property
  rcases hxrange with ⟨x₀, hx₀⟩
  rcases hyrange with ⟨y₀, hy₀⟩
  have hx₀' : T x₀ = (x : F) := hx₀
  have hy₀' : S y₀ = (y : E) := hy₀
  have hTinv : T.inverse x = (x₀ : E) :=
    T.inverse_apply_eq hTker hx₀'
  have hSinv : S.inverse y = (y₀ : F) :=
    S.inverse_apply_eq hSker hy₀'
  calc
    ⟪T.inverse x, (y : E)⟫_ℝ =
        ⟪(x₀ : E), S y₀⟫_ℝ := by rw [hTinv, hy₀']
    _ = ⟪T x₀, (y₀ : F)⟫_ℝ := (hformal x₀ y₀).symm
    _ = ⟪(x : F), S.inverse y⟫_ℝ := by rw [hx₀', hSinv]

private def realAdjointGraphSet (T : E →ₗ.[ℝ] F) : Set (F × E) :=
  {p | ∀ x : T.domain,
    ⟪p.snd, (x : E)⟫_ℝ = ⟪p.fst, T x⟫_ℝ}

private theorem realAdjointGraphSet_isClosed (T : E →ₗ.[ℝ] F) :
    _root_.IsClosed (realAdjointGraphSet T) := by
  rw [show realAdjointGraphSet T = ⋂ x : T.domain,
      {p : F × E |
        ⟪p.snd, (x : E)⟫_ℝ = ⟪p.fst, T x⟫_ℝ} by
    ext p
    simp [realAdjointGraphSet]]
  apply isClosed_iInter
  intro x
  apply isClosed_eq <;> fun_prop

/-- The maximal real adjoint is closed. -/
theorem realAdjoint_isClosed (T : E →ₗ.[ℝ] F)
    (hT : Dense (T.domain : Set E)) :
    (T.realAdjoint hT).IsClosed := by
  rw [LinearPMap.IsClosed]
  have hgraph :
      ((T.realAdjoint hT).graph : Set (F × E)) =
        realAdjointGraphSet T := by
    ext p
    constructor
    · intro hp x
      rcases (LinearPMap.mem_graph_iff (T.realAdjoint hT)).mp hp with
        ⟨y, hy, hvalue⟩
      rw [← hvalue, ← hy]
      exact T.realAdjoint_inner hT y x
    · intro hp
      have hy : p.fst ∈ (T.realAdjoint hT).domain := by
        change p.fst ∈ T.realAdjointDomain
        exact ⟨p.snd, hp⟩
      let y : (T.realAdjoint hT).domain := ⟨p.fst, hy⟩
      have hvalue : T.realAdjoint hT y = p.snd :=
        T.realAdjoint_apply_eq hT y hp
      exact (LinearPMap.mem_graph_iff (T.realAdjoint hT)).2
        ⟨y, rfl, hvalue⟩
  rw [hgraph]
  exact realAdjointGraphSet_isClosed T

/-! ## Passage of formal adjoints through graph closure -/

/-- Enlarging a dense operator domain preserves density. -/
theorem dense_domain_of_le
    {T S : E →ₗ.[ℝ] F}
    (hT : Dense (T.domain : Set E)) (hTS : T ≤ S) :
    Dense (S.domain : Set E) :=
  hT.mono hTS.1

/-- The closure of a densely defined partial linear map remains densely
defined. -/
theorem closure_dense_domain (T : E →ₗ.[ℝ] F)
    (hT : Dense (T.domain : Set E)) :
    Dense (T.closure.domain : Set E) :=
  dense_domain_of_le hT T.le_closure

/-- A formal-adjoint identity on the first operator's core extends to its
graph closure.  Both channels in the graph are retained while taking the
closure. -/
theorem formalAdjoint_closure_left
    (T : E →ₗ.[ℝ] F) (S : F →ₗ.[ℝ] E)
    (hT : T.IsClosable)
    (hformal : ∀ (x : T.domain) (y : S.domain),
      ⟪T x, (y : F)⟫_ℝ = ⟪(x : E), S y⟫_ℝ) :
    ∀ (x : T.closure.domain) (y : S.domain),
      ⟪T.closure x, (y : F)⟫_ℝ =
        ⟪(x : E), S y⟫_ℝ := by
  intro x y
  let annihilator : Set (E × F) :=
    {p | ⟪p.snd, (y : F)⟫_ℝ = ⟪p.fst, S y⟫_ℝ}
  have hannihilatorClosed : _root_.IsClosed annihilator := by
    apply isClosed_eq <;> fun_prop
  have hgraph : (T.graph : Set (E × F)) ⊆ annihilator := by
    intro p hp
    rcases (LinearPMap.mem_graph_iff T).mp hp with ⟨z, hz, hTz⟩
    change ⟪p.snd, (y : F)⟫_ℝ = ⟪p.fst, S y⟫_ℝ
    rw [← hTz, ← hz]
    exact hformal z y
  have hpairGraph : ((x : E), T.closure x) ∈ T.closure.graph :=
    (LinearPMap.mem_graph_iff T.closure).2 ⟨x, rfl, rfl⟩
  have hpairClosure : ((x : E), T.closure x) ∈
      _root_.closure (T.graph : Set (E × F)) := by
    rw [← Submodule.topologicalClosure_coe,
      hT.graph_closure_eq_closure_graph]
    exact hpairGraph
  exact closure_minimal hgraph hannihilatorClosed hpairClosure

/-- A closable operator has injective graph closure whenever one of its formal
adjoints has dense range.  A closure-kernel vector is orthogonal to that whole
range and therefore vanishes. -/
theorem closure_ker_eq_bot_of_denseRange_formalAdjoint
    (T : E →ₗ.[ℝ] F) (S : F →ₗ.[ℝ] E)
    (hT : T.IsClosable)
    (hformal : ∀ (x : T.domain) (y : S.domain),
      ⟪T x, (y : F)⟫_ℝ = ⟪(x : E), S y⟫_ℝ)
    (hSrange : Dense (LinearMap.range S.toFun : Set E)) :
    LinearMap.ker T.closure.toFun = ⊥ := by
  have hformalClosure := T.formalAdjoint_closure_left S hT hformal
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  apply hSrange.eq_zero_of_inner_left ℝ
  intro z hz
  rcases hz with ⟨y, rfl⟩
  have hxy := hformalClosure x y
  have hx' : T.closure x = 0 := hx
  rw [hx'] at hxy
  simpa using hxy.symm

/-- A formal adjoint of a closable densely defined core is contained in the
maximal real adjoint of the closed realization. -/
theorem le_realAdjoint_closure_of_formalAdjoint
    (T : E →ₗ.[ℝ] F) (S : F →ₗ.[ℝ] E)
    (hDense : Dense (T.domain : Set E))
    (hClosable : T.IsClosable)
    (hformal : ∀ (x : T.domain) (y : S.domain),
      ⟪T x, (y : F)⟫_ℝ = ⟪(x : E), S y⟫_ℝ) :
    S ≤ T.closure.realAdjoint (T.closure_dense_domain hDense) :=
  le_realAdjoint_of_formalAdjoint T.closure S
    (T.closure_dense_domain hDense)
    (T.formalAdjoint_closure_left S hClosable hformal)

/-! ## Maximal composition -/

/-- Ambient domain on which two real partial linear maps can be composed. -/
def realComposableDomain (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F) :
    Submodule ℝ E :=
  (g.domain.comap f.toFun).map f.domain.subtype

theorem realComposableDomain_le_domain
    (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F) :
    realComposableDomain g f ≤ f.domain := by
  rintro x ⟨y, _hy, rfl⟩
  exact y.property

private theorem domRestrict_realComposableDomain_mapsTo
    (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F)
    (x : (f.domRestrict (realComposableDomain g f)).domain) :
    f.domRestrict (realComposableDomain g f) x ∈ g.domain := by
  rcases x.property.1 with ⟨y, hy, hxy⟩
  have hambient : (x : E) = (y : E) := hxy.symm
  rw [LinearPMap.domRestrict_apply hambient]
  exact hy

/-- Maximal composition: its domain consists of all vectors in the domain of
`f` whose image lies in the domain of `g`. -/
def realMaximalComp (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F) :
    E →ₗ.[ℝ] G :=
  g.comp (f.domRestrict (realComposableDomain g f))
    (domRestrict_realComposableDomain_mapsTo g f)

@[simp] theorem realMaximalComp_domain
    (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F) :
    (realMaximalComp g f).domain = realComposableDomain g f := by
  change realComposableDomain g f ⊓ f.domain = realComposableDomain g f
  exact inf_eq_left.mpr (realComposableDomain_le_domain g f)

/-- Canonical domain element of the maximal composition from an element of
the first domain together with the proof that its image is in the second. -/
def realMaximalCompDomainMk
    (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F)
    (x : f.domain) (hx : f x ∈ g.domain) :
    (realMaximalComp g f).domain :=
  ⟨x, ⟨⟨x, hx, rfl⟩, x.property⟩⟩

/-- Maximal composition evaluates as the literal nested application on its
canonical domain constructor. -/
@[simp] theorem realMaximalComp_apply_mk
    (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F)
    (x : f.domain) (hx : f x ∈ g.domain) :
    realMaximalComp g f (realMaximalCompDomainMk g f x hx) =
      g ⟨f x, hx⟩ := by
  rfl

/-- First-domain component retained by an arbitrary element of a maximal
composition domain. -/
def realMaximalCompFirstDomain
    (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F)
    (x : (realMaximalComp g f).domain) : f.domain :=
  ⟨x, x.property.2⟩

/-- Second-domain component retained by an arbitrary element of a maximal
composition domain. -/
def realMaximalCompSecondDomain
    (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F)
    (x : (realMaximalComp g f).domain) : g.domain := by
  let xf := realMaximalCompFirstDomain g f x
  refine ⟨f xf, ?_⟩
  have h := domRestrict_realComposableDomain_mapsTo g f x
  exact h

/-- Evaluation of maximal composition through both retained domain
components. -/
theorem realMaximalComp_apply
    (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F)
    (x : (realMaximalComp g f).domain) :
    realMaximalComp g f x =
      g (realMaximalCompSecondDomain g f x) := by
  rfl

@[simp] theorem realMaximalCompFirstDomain_mk
    (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F)
    (x : f.domain) (hx : f x ∈ g.domain) :
    realMaximalCompFirstDomain g f
        (realMaximalCompDomainMk g f x hx) = x := by
  rfl

@[simp] theorem realMaximalCompSecondDomain_mk
    (g : F →ₗ.[ℝ] G) (f : E →ₗ.[ℝ] F)
    (x : f.domain) (hx : f x ∈ g.domain) :
    realMaximalCompSecondDomain g f
        (realMaximalCompDomainMk g f x hx) = ⟨f x, hx⟩ := by
  rfl

/-- Maximal adjoint square of a densely defined real partial linear map. -/
def realAdjointSquare (T : E →ₗ.[ℝ] F)
    (hT : Dense (T.domain : Set E)) : E →ₗ.[ℝ] E :=
  realMaximalComp (T.realAdjoint hT) T

end

end LinearPMap
