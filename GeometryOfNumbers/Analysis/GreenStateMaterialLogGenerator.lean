import GeometryOfNumbers.Analysis.NativeMaterialLogClock
import GeometryOfNumbers.Analysis.C2GreenWhiteningGenealogy

/-!
# Exact material reindexing of the native logarithmic clock

The material positive integer is `n=j+1`. This is neither a branch depth nor
an operator of heights. The maximal domain is transported, not replaced.
No transport through the Parseval analysis is constructed here.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp InnerProduct ComplexConjugate Topology ENNReal
namespace GeometryOfNumbers.Analysis.GreenStateMaterialLog
open GeometryOfNumbers.Analysis.NativeMaterialClock GreenFrame.Concrete
open GeometryOfNumbers.Analysis C2GlobalGreenBridge C2GreenTemporalMeanCanary

/-- Explicit positive-material address, with subtraction as its inverse. -/
def natEquivPNat : ℕ ≃ PNat where
  toFun j := ⟨j+1, by omega⟩
  invFun n := n.val-1
  left_inv j := by simp
  right_inv n := by apply Subtype.ext; change n.val-1+1 = n.val; have := n.pos; omega

@[simp] theorem natEquivPNat_val (j : ℕ) : (natEquivPNat j : ℕ) = j+1 := rfl
theorem natEquivPNat_symm (n : PNat) : natEquivPNat.symm n = n.val-1 := rfl
@[simp] theorem natEquivPNat_symm_add_one (n : PNat) :
    natEquivPNat.symm n + 1 = n.val := by change n.val-1+1 = n.val; have := n.pos; omega

private def reindex {α β : Type} (e : α ≃ β) (x : ℓ²(α,ℂ)) : ℓ²(β,ℂ) :=
  ⟨fun n => x (e.symm n), by
    change Memℓp (fun n => x (e.symm n)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact e.symm.summable_iff.mpr ((lp.memℓp x).summable (by norm_num))⟩

private def reindexLinearEquiv {α β : Type} (e : α ≃ β) : ℓ²(α,ℂ) ≃ₗ[ℂ] ℓ²(β,ℂ) where
  toFun := reindex e
  invFun := reindex e.symm
  left_inv x := by ext j; simp [reindex]
  right_inv x := by ext n; simp [reindex]
  map_add' x y := by ext n; rfl
  map_smul' c x := by ext n; rfl

/-- Canonical unitary reindexing; inner products are reindexed by an equivalence. -/
def nativeLogHilbertEquivGreenState : NativeLogHilbert ≃ₗᵢ[ℂ] State :=
  (reindexLinearEquiv natEquivPNat).isometryOfInner (by
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    exact natEquivPNat.symm.tsum_eq (fun j => inner ℂ (x j) (y j)))

@[simp] theorem nativeLogHilbertEquivGreenState_apply (x : NativeLogHilbert) (n : PNat) :
    nativeLogHilbertEquivGreenState x n = x (n.val-1) := rfl
@[simp] theorem nativeLogHilbertEquivGreenState_symm_apply (f : State) (j : ℕ) :
    nativeLogHilbertEquivGreenState.symm f j = f (natEquivPNat j) := rfl

theorem nativeLogHilbertEquivGreenState_norm (x : NativeLogHilbert) :
    ‖nativeLogHilbertEquivGreenState x‖ = ‖x‖ := nativeLogHilbertEquivGreenState.norm_map x

/-- The ordinary material delta, with no new basis structure. -/
def greenMaterialBasisVector (n : PNat) : State := lp.single 2 n 1

theorem nativeLogHilbertEquivGreenState_basisVector (j : ℕ) :
    nativeLogHilbertEquivGreenState (infiniteRealSpectralBasisVector j) =
      greenMaterialBasisVector (natEquivPNat j) := by
  ext n
  change (lp.single 2 j 1 : NativeLogHilbert) (natEquivPNat.symm n) =
    (lp.single 2 (natEquivPNat j) 1 : State) n
  by_cases hn : n = natEquivPNat j
  · subst n; simp [lp.single_apply]
  · have hj : natEquivPNat.symm n ≠ j := by
      intro h
      apply hn
      exact (natEquivPNat.apply_symm_apply n).symm.trans (congrArg natEquivPNat h)
    simp [lp.single_apply, hn, hj]

/-- Minimal conjugation of a partial operator: the domain is a submodule preimage. -/
private def unitaryTransport {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (L : H →ₗ.[ℂ] H) : K →ₗ.[ℂ] K where
  domain := L.domain.comap U.symm.toLinearEquiv.toLinearMap
  toFun := U.toLinearEquiv.toLinearMap.comp
    (L.toFun.comp (U.symm.toLinearEquiv.toLinearMap.domRestrict _ |>.codRestrict _
      (fun x => x.prop)))

private theorem unitaryTransport_apply {H K : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (L : H →ₗ.[ℂ] H) (f : (unitaryTransport U L).domain) :
    unitaryTransport U L f = U (L ⟨U.symm f.val, f.prop⟩) := rfl

/-- Exactly U L U⁻¹, including its transported maximal domain. -/
def greenStateMaterialLogGenerator : State →ₗ.[ℂ] State :=
  unitaryTransport nativeLogHilbertEquivGreenState nativeLogGenerator

theorem greenStateMaterialLogGenerator_mem_domain_iff (f : State) :
    f ∈ greenStateMaterialLogGenerator.domain ↔
    nativeLogHilbertEquivGreenState.symm f ∈ nativeLogGenerator.domain := Iff.rfl

theorem greenStateMaterialLogGenerator_domain_iff_memℓp (f : State) :
    f ∈ greenStateMaterialLogGenerator.domain ↔
    Memℓp (fun n : PNat => (Real.log (n : ℝ) : ℂ) * f n) 2 := by
  rw [greenStateMaterialLogGenerator_mem_domain_iff]
  change Memℓp (fun j : ℕ => (infiniteRealSpectralFrequency j : ℂ) *
    nativeLogHilbertEquivGreenState.symm f j) 2 ↔ _
  simp only [nativeLogHilbertEquivGreenState_symm_apply, infiniteRealSpectralFrequency]
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  exact natEquivPNat.summable_iff (f := fun n : PNat => ‖(Real.log (n : ℝ) : ℂ) * f n‖ ^ (2 : ℝ≥0∞).toReal)

theorem greenStateMaterialLogGenerator_apply (f : greenStateMaterialLogGenerator.domain)
    (n : PNat) : greenStateMaterialLogGenerator f n = (Real.log (n : ℝ) : ℂ) * f.val n := by
  change (infiniteRealSpectralFrequency (natEquivPNat.symm n) : ℂ) *
    nativeLogHilbertEquivGreenState.symm f.val (natEquivPNat.symm n) = _
  simp only [nativeLogHilbertEquivGreenState_symm_apply, infiniteRealSpectralFrequency,
    natEquivPNat_symm_add_one, natEquivPNat.apply_symm_apply]

theorem greenMaterialBasisVector_mem_domain (n : PNat) :
    greenMaterialBasisVector n ∈ greenStateMaterialLogGenerator.domain := by
  rw [← natEquivPNat.apply_symm_apply n, ← nativeLogHilbertEquivGreenState_basisVector]
  rw [greenStateMaterialLogGenerator_mem_domain_iff]
  simpa using nativeLogBasisVector_mem_domain (natEquivPNat.symm n)

theorem greenStateMaterialLogGenerator_basisVector_log (n : PNat) :
    greenStateMaterialLogGenerator ⟨greenMaterialBasisVector n, greenMaterialBasisVector_mem_domain n⟩ =
    (Real.log (n : ℝ) : ℂ) • greenMaterialBasisVector n := by
  let j := natEquivPNat.symm n
  have hb : greenMaterialBasisVector n =
      nativeLogHilbertEquivGreenState (infiniteRealSpectralBasisVector j) := by
    rw [nativeLogHilbertEquivGreenState_basisVector]; exact congrArg greenMaterialBasisVector
      (natEquivPNat.apply_symm_apply n).symm
  have hx : nativeLogHilbertEquivGreenState.symm (greenMaterialBasisVector n) =
      infiniteRealSpectralBasisVector j := by rw [hb]; simp
  let x : nativeLogGenerator.domain := ⟨nativeLogHilbertEquivGreenState.symm (greenMaterialBasisVector n),
    (greenStateMaterialLogGenerator_mem_domain_iff _).mp (greenMaterialBasisVector_mem_domain n)⟩
  change nativeLogHilbertEquivGreenState (nativeLogGenerator x) = _
  have he : x = ⟨infiniteRealSpectralBasisVector j, nativeLogBasisVector_mem_domain j⟩ :=
    Subtype.ext hx
  rw [he, nativeLogGenerator_basisVector_log, map_smul, ← hb]
  dsimp [j]
  rw [natEquivPNat_symm_add_one]


private theorem unitaryTransport_dense {H K : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (L : H →ₗ.[ℂ] H) (hL : Dense (L.domain : Set H)) :
    Dense ((unitaryTransport U L).domain : Set K) :=
  hL.preimage U.symm.toHomeomorph.isOpenMap

/-- This proof only uses unitary inner products and maximality of the adjoint. -/
private theorem unitaryTransport_isSelfAdjoint {H K : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : H ≃ₗᵢ[ℂ] K) (L : H →ₗ.[ℂ] H) (hL : IsSelfAdjoint L) :
    IsSelfAdjoint (unitaryTransport U L) := by
  let A := unitaryTransport U L
  have hLd := hL.dense_domain
  have hAd : Dense (A.domain : Set K) := unitaryTransport_dense U L hLd
  have hLeq : L.adjoint = L := LinearPMap.isSelfAdjoint_def.mp hL
  have hLf : L.IsFormalAdjoint L := by
    simpa only [hLeq] using (LinearPMap.adjoint_isFormalAdjoint hLd (T := L))
  have hAf : A.IsFormalAdjoint A := by
    intro x y
    have h := hLf ⟨U.symm x.val,x.prop⟩ ⟨U.symm y.val,y.prop⟩
    change inner ℂ (U (L ⟨U.symm x.val,x.prop⟩)) y.val =
      inner ℂ x.val (U (L ⟨U.symm y.val,y.prop⟩))
    calc
      _ = inner ℂ (L ⟨U.symm x.val,x.prop⟩) (U.symm y.val) := by
        simpa only [U.apply_symm_apply] using
          U.inner_map_map (L ⟨U.symm x.val,x.prop⟩) (U.symm y.val)
      _ = inner ℂ (U.symm x.val) (L ⟨U.symm y.val,y.prop⟩) := h
      _ = _ := by
        simpa only [U.apply_symm_apply] using
          (U.inner_map_map (U.symm x.val) (L ⟨U.symm y.val,y.prop⟩)).symm
  have hDom : A.adjoint.domain ≤ A.domain := by
    intro y hy
    let yA : A.adjoint.domain := ⟨y,hy⟩
    have hNative : U.symm y ∈ L.adjoint.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨U.symm (A.adjoint yA), ?_⟩
      intro x
      let xA : A.domain := ⟨U x.val, by change U.symm (U x.val) ∈ L.domain; simpa only [U.symm_apply_apply] using x.prop⟩
      have h := (LinearPMap.adjoint_isFormalAdjoint hAd (T := A)) yA xA
      have he : A xA = U (L x) := by
        change U (L ⟨U.symm (U x.val),_⟩) = U (L x)
        congr 2
        apply Subtype.ext
        simp
      rw [he] at h
      have hw := U.inner_map_map (U.symm (A.adjoint yA)) x.val
      have hv := U.inner_map_map (U.symm y) (L x)
      simp only [U.apply_symm_apply] at hw hv
      exact hw.symm.trans (h.trans hv)
    change U.symm y ∈ L.domain
    simpa only [hLeq] using hNative
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨hDom, ?_⟩
    intro x y hxy
    apply hAd.eq_of_inner_left ℂ
    intro z hz
    have hx := (LinearPMap.adjoint_isFormalAdjoint hAd (T := A)) x ⟨z,hz⟩
    have hy := hAf y ⟨z,hz⟩
    exact hx.trans (by rw [hxy]; exact hy.symm)
  · exact hAf.le_adjoint hAd

/-- Self-adjointness inherited from the native maximal generator by exact ULU⁻¹. -/
theorem greenStateMaterialLogGenerator_isSelfAdjoint :
    IsSelfAdjoint greenStateMaterialLogGenerator :=
  unitaryTransport_isSelfAdjoint nativeLogHilbertEquivGreenState
    nativeLogGenerator nativeLogGenerator_isSelfAdjoint

theorem greenStateMaterialLogGenerator_dense_domain :
    Dense (greenStateMaterialLogGenerator.domain : Set State) :=
  greenStateMaterialLogGenerator_isSelfAdjoint.dense_domain

theorem greenStateMaterialLogGenerator_isClosed :
    greenStateMaterialLogGenerator.IsClosed :=
  greenStateMaterialLogGenerator_isSelfAdjoint.isClosed

/-- Coordinate derivative, not a Hilbert differentiability or domain assertion. -/
theorem materialLogPhase_hasDerivAt (n : PNat) (a : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => phaseFactor (-s * Real.log (n : ℝ)) * a)
      (-Complex.I * (Real.log (n : ℝ) : ℂ) *
        (phaseFactor (-t * Real.log (n : ℝ)) * a)) t := by
  have h := (((hasDerivAt_id t).neg.mul_const (Real.log (n : ℝ))).ofReal_comp.mul_const
    Complex.I).cexp.mul_const a
  convert h using 1 <;> first
    | rfl
    | (simp only [phaseFactor, Pi.neg_apply, id_eq]; push_cast; ring)

theorem c2Source_materialLog_hasDerivAt (V : CoreState) (n : PNat) (t : ℝ) :
    HasDerivAt (fun s : ℝ => c2GlobalGreenInputIsometry s V n)
      (-Complex.I * (Real.log (n : ℝ) : ℂ) * c2GlobalGreenInputIsometry t V n) t := by
  have hf : (fun s : ℝ => c2GlobalGreenInputIsometry s V n) =
      (fun s => phaseFactor (-s * Real.log (n : ℝ)) * c2GlobalGreenInputIsometry 0 V n) :=
    funext (fun s => c2Source_phase s V n)
  rw [hf]
  rw [c2Source_phase t V n]
  exact materialLogPhase_hasDerivAt n (c2GlobalGreenInputIsometry 0 V n) t

/-- The additional logarithmic moment is an exact domain criterion. -/
theorem greenStateMaterialLogGenerator_domain_iff_log_moment (f : State) :
    f ∈ greenStateMaterialLogGenerator.domain ↔
    Summable (fun n : PNat => (Real.log (n : ℝ))^2 * ‖f n‖^2) := by
  rw [greenStateMaterialLogGenerator_domain_iff_memℓp,
    memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real,
    mul_pow, Real.norm_eq_abs, sq_abs]

/-- Time changes the phase only, so the domain gate is the same at every time. -/
theorem c2Source_log_domain_iff (t : ℝ) (V : CoreState) :
    c2GlobalGreenInputIsometry t V ∈ greenStateMaterialLogGenerator.domain ↔
    Summable (fun n : PNat => (Real.log (n : ℝ))^2 *
      Complex.normSq (c2GlobalGreenInputIsometry 0 V n)) := by
  rw [greenStateMaterialLogGenerator_domain_iff_log_moment]
  simp only [Complex.sq_norm, c2Source_normSq_time]

theorem c2Source_log_domain_time_independent (t s : ℝ) (V : CoreState) :
    c2GlobalGreenInputIsometry t V ∈ greenStateMaterialLogGenerator.domain ↔
    c2GlobalGreenInputIsometry s V ∈ greenStateMaterialLogGenerator.domain := by
  rw [c2Source_log_domain_iff, c2Source_log_domain_iff]

end GeometryOfNumbers.Analysis.GreenStateMaterialLog
