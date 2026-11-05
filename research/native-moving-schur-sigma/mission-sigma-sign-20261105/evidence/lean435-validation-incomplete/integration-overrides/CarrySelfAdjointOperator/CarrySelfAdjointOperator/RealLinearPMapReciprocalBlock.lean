import CarrySelfAdjointOperator.RealLinearPMapAdjointSquare
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic

/-!
# Reciprocal off-diagonal blocks of closed real operators

For a densely defined real operator `B : E -> F`, the reciprocal singular-value
operator is most naturally realized on the Hilbert sum `E \oplus F`.  If `B`
and its maximal adjoint are injective with dense range, put

`A = B⁻¹`, `C = (B*)⁻¹`.

The off-diagonal block

`H (x, y) = (C y, A x)`

is the signed reciprocal of the usual supersymmetric block associated with
`B`.  On singular eigenmodes, its positive and negative eigenvalues are the
reciprocal singular values of `B`.  Its square realizes the inverse of `B* B`
on the natural first-channel range, without requiring an unbounded Borel
functional-calculus API.
-/

open scoped InnerProductSpace RealInnerProductSpace

namespace LinearPMap

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A maximal real adjoint is injective when the original operator has dense
range. -/
theorem realAdjoint_ker_eq_bot_of_denseRange
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hRange : Dense (LinearMap.range T.toFun : Set F)) :
    (T.realAdjoint hDomain).ker = ⊥ := by
  rw [LinearPMap.ker_eq_bot]
  intro y hy
  apply Subtype.ext
  apply hRange.eq_zero_of_inner_left ℝ
  intro z hz
  rcases hz with ⟨x, rfl⟩
  have hadj := T.realAdjoint_inner hDomain y x
  have hy' : T.realAdjoint hDomain y = 0 := by
    exact hy
  have hzero : ⟪(y : F), T x⟫_ℝ = 0 := by
    rw [← hadj, hy']
    simp
  simpa [real_inner_comm] using hzero

/-- A vector satisfying the double-adjoint identity belongs to the graph of a
closed densely defined operator. -/
theorem mem_graph_of_forall_realAdjoint
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hClosed : T.IsClosed)
    {x : E} {y : F}
    (hpair : ∀ z : (T.realAdjoint hDomain).domain,
      ⟪y, (z : F)⟫_ℝ = ⟪x, T.realAdjoint hDomain z⟫_ℝ) :
    (x, y) ∈ T.graph := by
  let K := T.realGraphL2
  have hKclosed : _root_.IsClosed (K : Set (WithLp 2 (E × F))) :=
    T.realGraphL2_isClosed hClosed
  have hpDouble : WithLp.toLp 2 (x, y) ∈ Kᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro q hq
    have hqOrth : ∀ u : T.domain,
        ⟪(WithLp.ofLp q).1, (u : E)⟫_ℝ +
          ⟪(WithLp.ofLp q).2, T u⟫_ℝ = 0 := by
      intro u
      have hu : WithLp.toLp 2 ((u : E), T u) ∈ K :=
        T.toLp_mem_realGraphL2 u
      have horth := Submodule.inner_left_of_mem_orthogonal hu hq
      simpa [WithLp.prod_inner_apply] using horth
    have hsecond : (WithLp.ofLp q).2 ∈ T.realAdjointDomain := by
      refine ⟨-(WithLp.ofLp q).1, fun u => ?_⟩
      have h := hqOrth u
      rw [inner_neg_left]
      linarith
    let z : (T.realAdjoint hDomain).domain :=
      ⟨(WithLp.ofLp q).2, hsecond⟩
    have hadj : T.realAdjoint hDomain z = -(WithLp.ofLp q).1 := by
      apply T.realAdjoint_apply_eq hDomain z
      intro u
      have h := hqOrth u
      rw [inner_neg_left]
      linarith
    have hxy := hpair z
    rw [hadj] at hxy
    change
      ⟪x, (WithLp.ofLp q).1⟫_ℝ +
          ⟪y, (WithLp.ofLp q).2⟫_ℝ = 0
    rw [hxy, inner_neg_right]
    ring
  have hpClosure : WithLp.toLp 2 (x, y) ∈ K.topologicalClosure := by
    rw [← K.orthogonal_orthogonal_eq_closure]
    exact hpDouble
  have hpK : WithLp.toLp 2 (x, y) ∈ K := by
    rw [hKclosed.submodule_topologicalClosure_eq] at hpClosure
    exact hpClosure
  rcases hpK with ⟨p, hpGraph, hpEq⟩
  have hpEq' : (p : E × F) = (x, y) := by
    apply WithLp.toLp_injective (p := 2)
    simpa using hpEq
  simpa [hpEq'] using hpGraph

/-- The maximal real double adjoint of a closed densely defined operator is the
operator itself.  Density of the first adjoint domain is kept explicit because
it is exactly the closability condition used by reciprocal operators. -/
theorem realAdjoint_realAdjoint_eq_of_isClosed
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense
      ((T.realAdjoint hDomain).domain : Set F))
    (hClosed : T.IsClosed) :
    (T.realAdjoint hDomain).realAdjoint hAdjointDomain = T := by
  apply LinearPMap.ext
  · apply le_antisymm
    · intro x hx
      let xd : ((T.realAdjoint hDomain).realAdjoint
        hAdjointDomain).domain := ⟨x, hx⟩
      let y : F := (T.realAdjoint hDomain).realAdjoint
        hAdjointDomain xd
      have hpair : ∀ z : (T.realAdjoint hDomain).domain,
          ⟪y, (z : F)⟫_ℝ =
            ⟪x, T.realAdjoint hDomain z⟫_ℝ := by
        intro z
        exact (T.realAdjoint hDomain).realAdjoint_inner
          hAdjointDomain xd z
      have hgraph := T.mem_graph_of_forall_realAdjoint
        hDomain hClosed hpair
      rcases (LinearPMap.mem_graph_iff T).mp hgraph with
        ⟨x', hx', -⟩
      change (x' : E) = x at hx'
      exact hx' ▸ x'.property
    · intro x hx
      change x ∈ (T.realAdjoint hDomain).realAdjointDomain
      refine ⟨T ⟨x, hx⟩, fun z => ?_⟩
      rw [real_inner_comm,
        ← T.realAdjoint_isFormalAdjoint hDomain ⟨x, hx⟩ z,
        real_inner_comm]
  · intro x hxDouble hxT
    let xd : ((T.realAdjoint hDomain).realAdjoint
      hAdjointDomain).domain := ⟨x, hxDouble⟩
    have hgraph := T.mem_graph_of_forall_realAdjoint hDomain hClosed
      (x := x)
      (y := (T.realAdjoint hDomain).realAdjoint hAdjointDomain xd)
      (fun z => (T.realAdjoint hDomain).realAdjoint_inner
        hAdjointDomain xd z)
    rcases (LinearPMap.mem_graph_iff T).mp hgraph with
      ⟨x', hx', hvalue⟩
    have hxSubtype : x' = (⟨x, hxT⟩ : T.domain) :=
      Subtype.ext hx'
    simpa [xd, hxSubtype] using hvalue.symm

/-- The adjoint of an algebraic inverse is the inverse of the maximal adjoint,
provided both original maps are injective and the original range is dense. -/
theorem realAdjoint_inverse_eq_inverse_realAdjoint
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hRange : Dense (LinearMap.range T.toFun : Set F))
    (hKer : T.ker = ⊥)
    (hAdjointKer : (T.realAdjoint hDomain).ker = ⊥) :
    T.inverse.realAdjoint (by
      simpa only [LinearPMap.inverse_domain] using hRange) =
      (T.realAdjoint hDomain).inverse := by
  let A := T.inverse
  let S := T.realAdjoint hDomain
  have hA : Dense (A.domain : Set F) := by
    simpa [A, LinearPMap.inverse_domain] using hRange
  have hEq : A.realAdjoint hA = S.inverse := by
    apply le_antisymm
    · constructor
      · intro y hy
        let yd : (A.realAdjoint hA).domain := ⟨y, hy⟩
        let w : F := A.realAdjoint hA yd
        have hwDomain : w ∈ S.domain := by
          change w ∈ T.realAdjointDomain
          refine ⟨y, fun x => ?_⟩
          have hTx : T x ∈ A.domain := by
            simpa only [A, LinearPMap.inverse_domain] using
              (show T x ∈ LinearMap.range T.toFun from ⟨x, rfl⟩)
          let Ax : A.domain := ⟨T x, hTx⟩
          have hAx : A Ax = (x : E) :=
            T.inverse_apply_eq hKer rfl
          have hadj := A.realAdjoint_inner hA yd Ax
          rw [hAx] at hadj
          exact hadj.symm
        let wd : S.domain := ⟨w, hwDomain⟩
        have hSw : S wd = y := by
          apply T.realAdjoint_apply_eq hDomain wd
          intro x
          have hTx : T x ∈ A.domain := by
            simpa only [A, LinearPMap.inverse_domain] using
              (show T x ∈ LinearMap.range T.toFun from ⟨x, rfl⟩)
          let Ax : A.domain := ⟨T x, hTx⟩
          have hAx : A Ax = (x : E) :=
            T.inverse_apply_eq hKer rfl
          have hadj := A.realAdjoint_inner hA yd Ax
          rw [hAx] at hadj
          exact hadj.symm
        rw [LinearPMap.inverse_domain]
        exact ⟨wd, hSw⟩
      · intro y z hyz
        apply A.realAdjoint_apply_eq hA y
        intro x
        have hformal := T.inverse_formalAdjointIdentity S hKer hAdjointKer
          (T.realAdjoint_isFormalAdjoint hDomain) x z
        calc
          ⟪S.inverse z, (x : F)⟫_ℝ =
              ⟪(x : F), S.inverse z⟫_ℝ := real_inner_comm _ _
          _ = ⟪A x, (z : E)⟫_ℝ := hformal.symm
          _ = ⟪(y : E), A x⟫_ℝ := by
            rw [hyz]
            exact real_inner_comm _ _
    · exact A.le_realAdjoint_of_formalAdjoint S.inverse hA
        (T.inverse_formalAdjointIdentity S hKer hAdjointKer
          (T.realAdjoint_isFormalAdjoint hDomain))
  simpa only [A, S] using hEq

/-- Natural domain of an off-diagonal partial operator on an `L²` Hilbert sum. -/
def realOffDiagonalDomain (A : E →ₗ.[ℝ] F) (C : F →ₗ.[ℝ] E) :
    Submodule ℝ (WithLp 2 (E × F)) where
  carrier := {p | (WithLp.ofLp p).1 ∈ A.domain ∧
    (WithLp.ofLp p).2 ∈ C.domain}
  zero_mem' := by simp
  add_mem' hp hq := by
    exact ⟨A.domain.add_mem hp.1 hq.1, C.domain.add_mem hp.2 hq.2⟩
  smul_mem' r p hp := by
    exact ⟨A.domain.smul_mem r hp.1, C.domain.smul_mem r hp.2⟩

/-- First retained domain coordinate of an off-diagonal block. -/
def realOffDiagonalFirstDomain
    (A : E →ₗ.[ℝ] F) (C : F →ₗ.[ℝ] E)
    (p : realOffDiagonalDomain A C) : A.domain :=
  ⟨(WithLp.ofLp (p : WithLp 2 (E × F))).1, p.property.1⟩

/-- Second retained domain coordinate of an off-diagonal block. -/
def realOffDiagonalSecondDomain
    (A : E →ₗ.[ℝ] F) (C : F →ₗ.[ℝ] E)
    (p : realOffDiagonalDomain A C) : C.domain :=
  ⟨(WithLp.ofLp (p : WithLp 2 (E × F))).2, p.property.2⟩

/-- Off-diagonal block `H(x,y) = (C y, A x)` on the natural product domain. -/
def realOffDiagonal (A : E →ₗ.[ℝ] F) (C : F →ₗ.[ℝ] E) :
    WithLp 2 (E × F) →ₗ.[ℝ] WithLp 2 (E × F) where
  domain := realOffDiagonalDomain A C
  toFun :=
    { toFun := fun p => WithLp.toLp 2
        (C (realOffDiagonalSecondDomain A C p),
          A (realOffDiagonalFirstDomain A C p))
      map_add' := by
        intro p q
        apply WithLp.ofLp_injective (p := 2)
        apply Prod.ext
        · change C (realOffDiagonalSecondDomain A C (p + q)) =
            C (realOffDiagonalSecondDomain A C p) +
              C (realOffDiagonalSecondDomain A C q)
          rw [show realOffDiagonalSecondDomain A C (p + q) =
              realOffDiagonalSecondDomain A C p +
                realOffDiagonalSecondDomain A C q by
            apply Subtype.ext
            rfl]
          exact C.map_add _ _
        · change A (realOffDiagonalFirstDomain A C (p + q)) =
            A (realOffDiagonalFirstDomain A C p) +
              A (realOffDiagonalFirstDomain A C q)
          rw [show realOffDiagonalFirstDomain A C (p + q) =
              realOffDiagonalFirstDomain A C p +
                realOffDiagonalFirstDomain A C q by
            apply Subtype.ext
            rfl]
          exact A.map_add _ _
      map_smul' := by
        intro r p
        apply WithLp.ofLp_injective (p := 2)
        apply Prod.ext
        · change C (realOffDiagonalSecondDomain A C (r • p)) =
            r • C (realOffDiagonalSecondDomain A C p)
          rw [show realOffDiagonalSecondDomain A C (r • p) =
              r • realOffDiagonalSecondDomain A C p by
            apply Subtype.ext
            rfl]
          exact C.map_smul r _
        · change A (realOffDiagonalFirstDomain A C (r • p)) =
            r • A (realOffDiagonalFirstDomain A C p)
          rw [show realOffDiagonalFirstDomain A C (r • p) =
              r • realOffDiagonalFirstDomain A C p by
            apply Subtype.ext
            rfl]
          exact A.map_smul r _ }

@[simp] theorem realOffDiagonal_apply_ofLp
    (A : E →ₗ.[ℝ] F) (C : F →ₗ.[ℝ] E)
    (p : (realOffDiagonal A C).domain) :
    WithLp.ofLp (realOffDiagonal A C p) =
      (C (realOffDiagonalSecondDomain A C p),
        A (realOffDiagonalFirstDomain A C p)) :=
  rfl

/-- Product density gives density of the natural off-diagonal domain. -/
theorem realOffDiagonal_dense_domain
    (A : E →ₗ.[ℝ] F) (C : F →ₗ.[ℝ] E)
    (hA : Dense (A.domain : Set E))
    (hC : Dense (C.domain : Set F)) :
    Dense ((realOffDiagonal A C).domain : Set (WithLp 2 (E × F))) := by
  have hprod : Dense ((A.domain : Set E) ×ˢ (C.domain : Set F)) :=
    hA.prod hC
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm
  have himage : Dense (e '' ((A.domain : Set E) ×ˢ
      (C.domain : Set F))) :=
    e.toHomeomorph.isDenseEmbedding.dense_image.mpr hprod
  have hset : e '' ((A.domain : Set E) ×ˢ (C.domain : Set F)) =
      ((realOffDiagonal A C).domain : Set (WithLp 2 (E × F))) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change
        (WithLp.ofLp (WithLp.toLp 2 q)).1 ∈ A.domain ∧
          (WithLp.ofLp (WithLp.toLp 2 q)).2 ∈ C.domain
      change q.1 ∈ A.domain ∧ q.2 ∈ C.domain
      change q.1 ∈ A.domain ∧ q.2 ∈ C.domain at hq
      exact hq
    · intro hp
      change
        (WithLp.ofLp p).1 ∈ A.domain ∧
          (WithLp.ofLp p).2 ∈ C.domain at hp
      refine ⟨WithLp.ofLp p, hp, ?_⟩
      simp only [e, WithLp.prodContinuousLinearEquiv_symm_apply,
        WithLp.toLp_ofLp]
  rw [hset] at himage
  exact himage

/-- If the two channels are mutual maximal adjoints, their off-diagonal block
is literally equal to its maximal real adjoint. -/
theorem realAdjoint_realOffDiagonal_eq
    [CompleteSpace E] [CompleteSpace F]
    (A : E →ₗ.[ℝ] F) (C : F →ₗ.[ℝ] E)
    (hA : Dense (A.domain : Set E))
    (hC : Dense (C.domain : Set F))
    (hAC : A.realAdjoint hA = C)
    (hCA : C.realAdjoint hC = A) :
    (realOffDiagonal A C).realAdjoint
        (realOffDiagonal_dense_domain A C hA hC) =
      realOffDiagonal A C := by
  let H := realOffDiagonal A C
  let hH : Dense (H.domain : Set (WithLp 2 (E × F))) :=
    realOffDiagonal_dense_domain A C hA hC
  have hformal : ∀ (p q : H.domain),
      ⟪H p, (q : WithLp 2 (E × F))⟫_ℝ =
        ⟪(p : WithLp 2 (E × F)), H q⟫_ℝ := by
    intro p q
    let px : A.domain := realOffDiagonalFirstDomain A C p
    let py : C.domain := realOffDiagonalSecondDomain A C p
    let qx : A.domain := realOffDiagonalFirstDomain A C q
    let qy : C.domain := realOffDiagonalSecondDomain A C q
    have hqy : (qy : F) ∈ (A.realAdjoint hA).domain := by
      rw [hAC]
      exact qy.property
    have hqx : (qx : E) ∈ (C.realAdjoint hC).domain := by
      rw [hCA]
      exact qx.property
    have hAf : ⟪A px, (qy : F)⟫_ℝ =
        ⟪(px : E), C qy⟫_ℝ := by
      have h := A.realAdjoint_isFormalAdjoint hA px ⟨qy, hqy⟩
      have hvalue : A.realAdjoint hA ⟨qy, hqy⟩ = C qy := by
        cases hAC
        rfl
      rw [hvalue] at h
      exact h
    have hCf : ⟪C py, (qx : E)⟫_ℝ =
        ⟪(py : F), A qx⟫_ℝ := by
      have h := C.realAdjoint_isFormalAdjoint hC py ⟨qx, hqx⟩
      have hvalue : C.realAdjoint hC ⟨qx, hqx⟩ = A qx := by
        cases hCA
        rfl
      rw [hvalue] at h
      exact h
    change
      ⟪C py, (qx : E)⟫_ℝ + ⟪A px, (qy : F)⟫_ℝ =
        ⟪(px : E), C qy⟫_ℝ + ⟪(py : F), A qx⟫_ℝ
    rw [hAf, hCf]
    ring
  have hEq : H.realAdjoint hH = H := by
    apply le_antisymm
    · constructor
      · intro p hp
        let pd : (H.realAdjoint hH).domain := ⟨p, hp⟩
        have hvA : (WithLp.ofLp p).2 ∈ A.realAdjointDomain := by
          refine ⟨(WithLp.ofLp (H.realAdjoint hH pd)).1, fun x => ?_⟩
          let q : H.domain := ⟨WithLp.toLp 2 ((x : E), 0),
            ⟨x.property, C.domain.zero_mem⟩⟩
          have hqFirst : realOffDiagonalFirstDomain A C q = x := by
            apply Subtype.ext
            rfl
          have hqSecond : realOffDiagonalSecondDomain A C q = 0 := by
            apply Subtype.ext
            rfl
          have hadj := H.realAdjoint_inner hH pd q
          simpa [q, pd, H, realOffDiagonal_apply_ofLp,
            hqFirst, hqSecond, WithLp.prod_inner_apply] using hadj
        have huC : (WithLp.ofLp p).1 ∈ C.realAdjointDomain := by
          refine ⟨(WithLp.ofLp (H.realAdjoint hH pd)).2, fun y => ?_⟩
          let q : H.domain := ⟨WithLp.toLp 2 (0, (y : F)),
            ⟨A.domain.zero_mem, y.property⟩⟩
          have hqFirst : realOffDiagonalFirstDomain A C q = 0 := by
            apply Subtype.ext
            rfl
          have hqSecond : realOffDiagonalSecondDomain A C q = y := by
            apply Subtype.ext
            rfl
          have hadj := H.realAdjoint_inner hH pd q
          simpa [q, pd, H, realOffDiagonal_apply_ofLp,
            hqFirst, hqSecond, WithLp.prod_inner_apply] using hadj
        have hvC : (WithLp.ofLp p).2 ∈ C.domain := by
          rw [← hAC]
          exact hvA
        have huA : (WithLp.ofLp p).1 ∈ A.domain := by
          rw [← hCA]
          exact huC
        exact ⟨huA, hvC⟩
      · intro p q hpq
        apply H.realAdjoint_apply_eq hH p
        intro z
        have hsymmetric := hformal q z
        rw [← hpq] at hsymmetric
        exact hsymmetric
    · exact H.le_realAdjoint_of_formalAdjoint H hH hformal
  simpa only [H] using hEq

/-! ## Reciprocal block of one closed operator -/

/-- Canonical reciprocal off-diagonal block attached to a densely defined
operator `T`. -/
def realReciprocalOffDiagonal
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E)) :
    WithLp 2 (E × F) →ₗ.[ℝ] WithLp 2 (E × F) :=
  realOffDiagonal (T.realAdjoint hDomain).inverse T.inverse

/-- Dense ranges of `T` and `T*` are exactly density of the two natural
inverse-channel domains. -/
theorem realReciprocalOffDiagonal_dense_domain
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hRange : Dense (LinearMap.range T.toFun : Set F))
    (hAdjointRange : Dense
      (LinearMap.range (T.realAdjoint hDomain).toFun : Set E)) :
    Dense ((T.realReciprocalOffDiagonal hDomain).domain :
      Set (WithLp 2 (E × F))) := by
  exact realOffDiagonal_dense_domain
    (T.realAdjoint hDomain).inverse T.inverse
    (by simpa only [LinearPMap.inverse_domain] using hAdjointRange)
    (by simpa only [LinearPMap.inverse_domain] using hRange)

/-- First retained domain coordinate of the maximal adjoint square. -/
def realAdjointSquareFirstDomain
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (x : (T.realAdjointSquare hDomain).domain) : T.domain := by
  change (realMaximalComp (T.realAdjoint hDomain) T).domain at x
  exact realMaximalCompFirstDomain (T.realAdjoint hDomain) T x

/-- Second retained domain coordinate of the maximal adjoint square. -/
def realAdjointSquareSecondDomain
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (x : (T.realAdjointSquare hDomain).domain) :
    (T.realAdjoint hDomain).domain := by
  change (realMaximalComp (T.realAdjoint hDomain) T).domain at x
  exact realMaximalCompSecondDomain (T.realAdjoint hDomain) T x

/-- Evaluation of the adjoint square through its retained second coordinate. -/
theorem realAdjointSquare_apply_retained
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (x : (T.realAdjointSquare hDomain).domain) :
    T.realAdjointSquare hDomain x =
      T.realAdjoint hDomain
        (T.realAdjointSquareSecondDomain hDomain x) := by
  change realMaximalComp (T.realAdjoint hDomain) T x = _
  exact realMaximalComp_apply (T.realAdjoint hDomain) T x

/-! ## The signed generator before reciprocal inversion -/

/-- Canonical off-diagonal signed generator `[[0, T*], [T, 0]]`.  Its
reciprocal on the nonzero support is the signed-height operator constructed
below. -/
def realAdjointOffDiagonal
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E)) :
    WithLp 2 (E × F) →ₗ.[ℝ] WithLp 2 (E × F) :=
  realOffDiagonal T (T.realAdjoint hDomain)

/-- Dense domains of `T` and `T*` give the natural dense domain of the
signed generator. -/
theorem realAdjointOffDiagonal_dense_domain
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense
      ((T.realAdjoint hDomain).domain : Set F)) :
    Dense ((T.realAdjointOffDiagonal hDomain).domain :
      Set (WithLp 2 (E × F))) := by
  exact realOffDiagonal_dense_domain T (T.realAdjoint hDomain)
    hDomain hAdjointDomain

/-- Exact action of the maximal-adjoint off-diagonal block on a pair of
domain vectors. -/
@[simp] theorem realOffDiagonal_apply_domainPair
    (A : E →ₗ.[ℝ] F) (C : F →ₗ.[ℝ] E)
    (x : A.domain) (y : C.domain) :
    realOffDiagonal A C
        ⟨WithLp.toLp 2 ((x : E), (y : F)), ⟨x.property, y.property⟩⟩ =
      WithLp.toLp 2 (C y, A x) := by
  apply WithLp.ofLp_injective 2
  rw [realOffDiagonal_apply_ofLp]
  rfl

/-- A closed densely defined operator and its maximal adjoint form a maximal
self-adjoint signed generator. -/
theorem realAdjoint_realAdjointOffDiagonal_eq
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense
      ((T.realAdjoint hDomain).domain : Set F))
    (hClosed : T.IsClosed) :
    (T.realAdjointOffDiagonal hDomain).realAdjoint
        (T.realAdjointOffDiagonal_dense_domain
          hDomain hAdjointDomain) =
      T.realAdjointOffDiagonal hDomain := by
  exact realAdjoint_realOffDiagonal_eq T (T.realAdjoint hDomain)
    hDomain hAdjointDomain rfl
      (T.realAdjoint_realAdjoint_eq_of_isClosed
        hDomain hAdjointDomain hClosed)

/-- Even-sector domain vector retained by the signed generator from one
vector in the maximal adjoint-square domain. -/
def realAdjointOffDiagonalEvenSquareInput
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (x : (T.realAdjointSquare hDomain).domain) :
    (realOffDiagonal T (T.realAdjoint hDomain)).domain :=
  ⟨WithLp.toLp 2
      ((T.realAdjointSquareFirstDomain hDomain x : E), 0),
    ⟨(T.realAdjointSquareFirstDomain hDomain x).property,
      (T.realAdjoint hDomain).domain.zero_mem⟩⟩

/-- One signed-generator step sends the retained even vector to the retained
odd vector `T x`. -/
theorem realAdjointOffDiagonal_apply_evenSquareInput
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (x : (T.realAdjointSquare hDomain).domain) :
    WithLp.ofLp
        (T.realAdjointOffDiagonal hDomain
          (T.realAdjointOffDiagonalEvenSquareInput hDomain x)) =
      (0, (T.realAdjointSquareSecondDomain hDomain x : F)) := by
  change WithLp.ofLp
      (realOffDiagonal T (T.realAdjoint hDomain) _) = _
  rw [realOffDiagonal_apply_ofLp]
  have hfirst : realOffDiagonalFirstDomain T (T.realAdjoint hDomain)
      (T.realAdjointOffDiagonalEvenSquareInput hDomain x) =
        T.realAdjointSquareFirstDomain hDomain x := by
    apply Subtype.ext
    rfl
  have hsecond : realOffDiagonalSecondDomain T (T.realAdjoint hDomain)
      (T.realAdjointOffDiagonalEvenSquareInput hDomain x) = 0 := by
    apply Subtype.ext
    rfl
  rw [hfirst, hsecond, (T.realAdjoint hDomain).map_zero]
  apply Prod.ext
  · rfl
  · rfl

/-- Odd-sector domain vector retained by the signed generator from the same
maximal square-domain vector. -/
def realAdjointOffDiagonalOddSquareInput
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (x : (T.realAdjointSquare hDomain).domain) :
    (realOffDiagonal T (T.realAdjoint hDomain)).domain :=
  ⟨WithLp.toLp 2
      (0, (T.realAdjointSquareSecondDomain hDomain x : F)),
    ⟨T.domain.zero_mem,
      (T.realAdjointSquareSecondDomain hDomain x).property⟩⟩

/-- The next signed-generator step is exactly the maximal adjoint-square
action on the even channel. -/
theorem realAdjointOffDiagonal_apply_oddSquareInput
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (x : (T.realAdjointSquare hDomain).domain) :
    WithLp.ofLp
        (T.realAdjointOffDiagonal hDomain
          (T.realAdjointOffDiagonalOddSquareInput hDomain x)) =
      (T.realAdjointSquare hDomain x, 0) := by
  change WithLp.ofLp
      (realOffDiagonal T (T.realAdjoint hDomain) _) = _
  rw [realOffDiagonal_apply_ofLp]
  have hfirst : realOffDiagonalFirstDomain T (T.realAdjoint hDomain)
      (T.realAdjointOffDiagonalOddSquareInput hDomain x) = 0 := by
    apply Subtype.ext
    rfl
  have hsecond : realOffDiagonalSecondDomain T (T.realAdjoint hDomain)
      (T.realAdjointOffDiagonalOddSquareInput hDomain x) =
        T.realAdjointSquareSecondDomain hDomain x := by
    apply Subtype.ext
    rfl
  rw [hfirst, hsecond, T.map_zero]
  apply Prod.ext
  · exact T.realAdjointSquare_apply_retained hDomain x
  · rfl

/-- Canonical first input for the exact two-step reciprocal identity.  It is
the even-channel vector `(T* T x, 0)`. -/
def realReciprocalOffDiagonalFirstSquareInput
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (x : (T.realAdjointSquare hDomain).domain) :
    (realOffDiagonal (T.realAdjoint hDomain).inverse T.inverse).domain := by
  let S := T.realAdjoint hDomain
  refine ⟨WithLp.toLp 2 (T.realAdjointSquare hDomain x, 0), ?_⟩
  change T.realAdjointSquare hDomain x ∈ S.inverse.domain ∧
    0 ∈ T.inverse.domain
  constructor
  · rw [LinearPMap.inverse_domain]
    refine ⟨T.realAdjointSquareSecondDomain hDomain x, ?_⟩
    exact (T.realAdjointSquare_apply_retained hDomain x).symm
  · rw [LinearPMap.inverse_domain]
    exact ⟨0, by simp⟩

/-- One reciprocal step sends `(T* T x, 0)` exactly to `(0, T x)`. -/
theorem realReciprocalOffDiagonal_apply_firstSquareInput
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointKer : (T.realAdjoint hDomain).ker = ⊥)
    (x : (T.realAdjointSquare hDomain).domain) :
    WithLp.ofLp
        (T.realReciprocalOffDiagonal hDomain
      (T.realReciprocalOffDiagonalFirstSquareInput hDomain x)) =
      (0, T (T.realAdjointSquareFirstDomain hDomain x)) := by
  let S := T.realAdjoint hDomain
  let p := T.realReciprocalOffDiagonalFirstSquareInput hDomain x
  change WithLp.ofLp (realOffDiagonal S.inverse T.inverse p) = _
  rw [realOffDiagonal_apply_ofLp]
  apply Prod.ext
  · change T.inverse (realOffDiagonalSecondDomain
        S.inverse T.inverse p) = 0
    have hzero : realOffDiagonalSecondDomain
        S.inverse T.inverse p = 0 := by
      apply Subtype.ext
      rfl
    rw [hzero]
    exact T.inverse.map_zero
  · change S.inverse (realOffDiagonalFirstDomain
        S.inverse T.inverse p) =
      T (T.realAdjointSquareFirstDomain hDomain x)
    have hinverse : S.inverse (realOffDiagonalFirstDomain
        S.inverse T.inverse p) =
        (T.realAdjointSquareSecondDomain hDomain x : F) := by
      apply S.inverse_apply_eq hAdjointKer
      exact (T.realAdjointSquare_apply_retained hDomain x).symm
    exact hinverse

/-- Canonical second input for the exact two-step reciprocal identity. -/
def realReciprocalOffDiagonalSecondSquareInput
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointKer : (T.realAdjoint hDomain).ker = ⊥)
    (x : (T.realAdjointSquare hDomain).domain) :
    (realOffDiagonal (T.realAdjoint hDomain).inverse T.inverse).domain := by
  let H := T.realReciprocalOffDiagonal hDomain
  let p := T.realReciprocalOffDiagonalFirstSquareInput hDomain x
  refine ⟨H p, ?_⟩
  change (WithLp.ofLp (H p)).1 ∈
      (T.realAdjoint hDomain).inverse.domain ∧
    (WithLp.ofLp (H p)).2 ∈ T.inverse.domain
  rw [T.realReciprocalOffDiagonal_apply_firstSquareInput
    hDomain hAdjointKer x]
  constructor
  · rw [LinearPMap.inverse_domain]
    exact ⟨0, (T.realAdjoint hDomain).map_zero⟩
  · rw [LinearPMap.inverse_domain]
    exact ⟨T.realAdjointSquareFirstDomain hDomain x, rfl⟩

/-- Exact reciprocal-square identity on the natural range of `T* T`:
`H² (T* T x, 0) = (x, 0)`. -/
theorem realReciprocalOffDiagonal_apply_secondSquareInput
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hKer : T.ker = ⊥)
    (hAdjointKer : (T.realAdjoint hDomain).ker = ⊥)
    (x : (T.realAdjointSquare hDomain).domain) :
    WithLp.ofLp
        (T.realReciprocalOffDiagonal hDomain
          (T.realReciprocalOffDiagonalSecondSquareInput
            hDomain hAdjointKer x)) =
      ((x : E), 0) := by
  let S := T.realAdjoint hDomain
  let q := T.realReciprocalOffDiagonalSecondSquareInput
    hDomain hAdjointKer x
  change WithLp.ofLp (realOffDiagonal S.inverse T.inverse q) = _
  rw [realOffDiagonal_apply_ofLp]
  apply Prod.ext
  · change T.inverse (realOffDiagonalSecondDomain
        S.inverse T.inverse q) = (x : E)
    have hvalue : (realOffDiagonalSecondDomain
        S.inverse T.inverse q : F) =
        T (T.realAdjointSquareFirstDomain hDomain x) := by
      exact congrArg Prod.snd
        (T.realReciprocalOffDiagonal_apply_firstSquareInput
          hDomain hAdjointKer x)
    have hinverse : T.inverse (realOffDiagonalSecondDomain
        S.inverse T.inverse q) =
        (T.realAdjointSquareFirstDomain hDomain x : E) := by
      apply T.inverse_apply_eq hKer
      exact hvalue.symm
    exact hinverse
  · change S.inverse (realOffDiagonalFirstDomain
        S.inverse T.inverse q) = 0
    have hzero : realOffDiagonalFirstDomain
        S.inverse T.inverse q = 0 := by
      apply Subtype.ext
      exact congrArg Prod.fst
        (T.realReciprocalOffDiagonal_apply_firstSquareInput
          hDomain hAdjointKer x)
    rw [hzero]
    exact S.inverse.map_zero

/-- A closed injective operator with dense domain and range, whose adjoint also
has dense domain and range, has a maximal self-adjoint reciprocal block. -/
theorem realAdjoint_realReciprocalOffDiagonal_eq
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense
      ((T.realAdjoint hDomain).domain : Set F))
    (hClosed : T.IsClosed)
    (hRange : Dense (LinearMap.range T.toFun : Set F))
    (hAdjointRange : Dense
      (LinearMap.range (T.realAdjoint hDomain).toFun : Set E))
    (hKer : T.ker = ⊥) :
    (T.realReciprocalOffDiagonal hDomain).realAdjoint
        (T.realReciprocalOffDiagonal_dense_domain
          hDomain hRange hAdjointRange) =
      T.realReciprocalOffDiagonal hDomain := by
  let S := T.realAdjoint hDomain
  have hSKer : S.ker = ⊥ :=
    T.realAdjoint_ker_eq_bot_of_denseRange hDomain hRange
  have hdouble : S.realAdjoint hAdjointDomain = T :=
    T.realAdjoint_realAdjoint_eq_of_isClosed
      hDomain hAdjointDomain hClosed
  have hdoubleKer : (S.realAdjoint hAdjointDomain).ker = ⊥ := by
    rw [hdouble]
    exact hKer
  have hSinverseDomain : Dense (S.inverse.domain : Set E) := by
    simpa only [LinearPMap.inverse_domain] using hAdjointRange
  have hTinverseDomain : Dense (T.inverse.domain : Set F) := by
    simpa only [LinearPMap.inverse_domain] using hRange
  have hleft : S.inverse.realAdjoint hSinverseDomain = T.inverse := by
    have h := S.realAdjoint_inverse_eq_inverse_realAdjoint
      hAdjointDomain hAdjointRange hSKer hdoubleKer
    rw [hdouble] at h
    exact h
  have hright : T.inverse.realAdjoint hTinverseDomain = S.inverse :=
    T.realAdjoint_inverse_eq_inverse_realAdjoint
      hDomain hRange hKer hSKer
  exact realAdjoint_realOffDiagonal_eq S.inverse T.inverse
    hSinverseDomain hTinverseDomain hleft hright

/-- The reciprocal block is closed as an immediate consequence of maximal
self-adjointness. -/
theorem realReciprocalOffDiagonal_isClosed
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense
      ((T.realAdjoint hDomain).domain : Set F))
    (hClosed : T.IsClosed)
    (hRange : Dense (LinearMap.range T.toFun : Set F))
    (hAdjointRange : Dense
      (LinearMap.range (T.realAdjoint hDomain).toFun : Set E))
    (hKer : T.ker = ⊥) :
    (T.realReciprocalOffDiagonal hDomain).IsClosed := by
  have hadjointClosed :=
    (T.realReciprocalOffDiagonal hDomain).realAdjoint_isClosed
      (T.realReciprocalOffDiagonal_dense_domain
        hDomain hRange hAdjointRange)
  rw [T.realAdjoint_realReciprocalOffDiagonal_eq hDomain
    hAdjointDomain hClosed hRange hAdjointRange hKer] at hadjointClosed
  exact hadjointClosed

/-- A partial real operator bundled with its dense-domain maximal
self-adjointness certificate.  Bundling keeps proof-dependent adjoint domains
opaque when a concrete application exports the operator. -/
structure RealMaximalSelfAdjointData (G : Type*)
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] where
  operator : G →ₗ.[ℝ] G
  denseDomain : Dense (operator.domain : Set G)
  adjoint_eq : operator.realAdjoint denseDomain = operator

/-- Bundled reciprocal block of a closed operator satisfying the exact
injectivity and density gates. -/
def realReciprocalOffDiagonalSelfAdjointData
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense
      ((T.realAdjoint hDomain).domain : Set F))
    (hClosed : T.IsClosed)
    (hRange : Dense (LinearMap.range T.toFun : Set F))
    (hAdjointRange : Dense
      (LinearMap.range (T.realAdjoint hDomain).toFun : Set E))
    (hKer : T.ker = ⊥) :
    RealMaximalSelfAdjointData (WithLp 2 (E × F)) where
  operator := T.realReciprocalOffDiagonal hDomain
  denseDomain := T.realReciprocalOffDiagonal_dense_domain
    hDomain hRange hAdjointRange
  adjoint_eq := T.realAdjoint_realReciprocalOffDiagonal_eq hDomain
    hAdjointDomain hClosed hRange hAdjointRange hKer

/-- Every bundled maximal self-adjoint operator is closed. -/
theorem RealMaximalSelfAdjointData.isClosed
    (data : RealMaximalSelfAdjointData E) :
    data.operator.IsClosed := by
  have hadjointClosed := data.operator.realAdjoint_isClosed data.denseDomain
  rw [data.adjoint_eq] at hadjointClosed
  exact hadjointClosed

/-- Bundled maximal self-adjoint signed generator `[[0, T*], [T, 0]]`.
Unlike the reciprocal signed-height operator, this construction needs no
injectivity or range hypothesis. -/
def realAdjointOffDiagonalSelfAdjointData
    [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ.[ℝ] F)
    (hDomain : Dense (T.domain : Set E))
    (hAdjointDomain : Dense
      ((T.realAdjoint hDomain).domain : Set F))
    (hClosed : T.IsClosed) :
    RealMaximalSelfAdjointData (WithLp 2 (E × F)) where
  operator := T.realAdjointOffDiagonal hDomain
  denseDomain := T.realAdjointOffDiagonal_dense_domain
    hDomain hAdjointDomain
  adjoint_eq := T.realAdjoint_realAdjointOffDiagonal_eq
    hDomain hAdjointDomain hClosed

end

end LinearPMap
