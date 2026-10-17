import JetCompatibility

/-! A coherent tower of physical LIMIT IMAGE spaces, conditional on the
actual return estimates. The spaces come from physical port limits, and the
transition maps are induced by the SAME source coefficients. No new metric
or moment-Gram quotient is used. This is not a single ambient infinite family. -/
namespace CarryReturnCompatibility
open CarrySelfAdjointOperator CarrySelfAdjointOperator.ChiralReturn
open GeometryOfNumbers.Analysis CarryCorrectedGreenPorts
open CarryMaterialMixedSchurComparison
open Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def AllFiniteReturnBounds : Prop :=
  ∀ N : ℕ, ∀ᶠ k : ℕ in atTop, ‖radialReturnTransfer k (N+1)‖ ≤ 1

/-- A diagonal exhaustion of genuine regularized finite diagrams. The
cutoff grows with the order; no single k for all dimensions is asserted. -/
theorem allFiniteReturnBounds_diagonal_schedule (hc : AllFiniteReturnBounds) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∀ n N : ℕ, N ≤ n →
      ‖radialReturnTransfer (rho n) (N+1)‖ ≤ 1 := by
  have hh (n : ℕ) : ∃ K : ℕ, ∀ k ≥ K, ‖radialReturnTransfer k (n+1)‖ ≤ 1 :=
    Filter.eventually_atTop.mp (hc n)
  choose K hK using hh
  let rho : ℕ → ℕ := fun n => n+Finset.sup (Finset.range (n+1)) K
  have hm : StrictMono rho := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hs : Finset.sup (Finset.range (n+1)) K ≤ Finset.sup (Finset.range (n+1+1)) K :=
      Finset.sup_mono (Finset.range_mono (by omega))
    dsimp [rho]
    omega
  refine ⟨rho,hm,?_⟩
  intro n N hN
  have hKn : K n ≤ Finset.sup (Finset.range (n+1)) K :=
    Finset.le_sup (f := K) (by simp)
  have hk := hK n (rho n) (by dsimp [rho]; omega)
  exact radialReturnTransfer_norm_le_one_of_prefix (rho n) (by omega : N+1 ≤ n+1) hk

/-- Each choice is a limit of the physical ports, through the compactness
theorem of PR #25. Its norm is inherited from the old physical L2. -/
def limitBlock (hc : AllFiniteReturnBounds) (N : ℕ) :
    Fin (N+1) → CanonicalCompletedNativeChiralCauchyCarrier :=
  Classical.choose (correctedGreen_realization_of_contractive N (hc N) 1 (by norm_num))

theorem limitBlock_pairing (hc : AllFiniteReturnBounds) (N : ℕ) (a b : Fin (N+1)) :
    inner ℂ (limitBlock hc N a) (limitBlock hc N b) =
      carryKernelJet (fun t u => (carryMaterialRealResidual t u : ℂ)) a.val b.val := by
  have h := (Classical.choose_spec
    (correctedGreen_realization_of_contractive N (hc N) 1 (by norm_num))).2 a b
  rw [material_valve_confluent_jet 1 (by norm_num)] at h
  exact h

def finitePhysicalSynthesis {index : Type*} [Fintype index]
    (v : index → CanonicalCompletedNativeChiralCauchyCarrier) :
    (index → ℂ) →ₗ[ℂ] CanonicalCompletedNativeChiralCauchyCarrier where
  toFun x := ∑ a, x a • v a
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

theorem finitePhysicalSynthesis_pairing {index : Type*} [Fintype index]
    (v : index → CanonicalCompletedNativeChiralCauchyCarrier) (x y : index → ℂ) :
    inner ℂ (finitePhysicalSynthesis v x) (finitePhysicalSynthesis v y) =
      ∑ a, ∑ b, conj (x a)*y b*inner ℂ (v a) (v b) := by
  simp only [finitePhysicalSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem finitePhysicalSynthesis_pad {N M : ℕ} (h : N ≤ M)
    (v : Fin M → CanonicalCompletedNativeChiralCauchyCarrier) (x : Fin N → ℂ) :
    finitePhysicalSynthesis v (radialSourcePad h x) =
      finitePhysicalSynthesis (fun a => v (Fin.castLE h a)) x := by
  classical
  rw [radialSourcePad, map_sum]
  simp [finitePhysicalSynthesis]

/-- Compatibility of complete limit pairings, not equality of independently
chosen ambient physical representatives. Both inputs are arbitrary. -/
theorem limitBlock_prefix_pairing (hc : AllFiniteReturnBounds) {N M : ℕ} (h : N ≤ M)
    (x y : Fin (N+1) → ℂ) :
    inner ℂ
      (finitePhysicalSynthesis (fun a => limitBlock hc M (Fin.castLE (Nat.add_le_add_right h 1) a)) x)
      (finitePhysicalSynthesis (fun a => limitBlock hc M (Fin.castLE (Nat.add_le_add_right h 1) a)) y) =
    inner ℂ (finitePhysicalSynthesis (limitBlock hc N) x) (finitePhysicalSynthesis (limitBlock hc N) y) := by
  simp only [finitePhysicalSynthesis_pairing, limitBlock_pairing, Fin.val_castLE]

theorem limitBlock_prefix_norm (hc : AllFiniteReturnBounds) {N M : ℕ} (h : N ≤ M)
    (x : Fin (N+1) → ℂ) :
    ‖finitePhysicalSynthesis (fun a => limitBlock hc M (Fin.castLE (Nat.add_le_add_right h 1) a)) x‖ =
      ‖finitePhysicalSynthesis (limitBlock hc N) x‖ := by
  have he : ‖finitePhysicalSynthesis (fun a => limitBlock hc M (Fin.castLE (Nat.add_le_add_right h 1) a)) x‖^2 =
      ‖finitePhysicalSynthesis (limitBlock hc N) x‖^2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
    exact congrArg RCLike.re (limitBlock_prefix_pairing hc h x x)
  nlinarith [norm_nonneg (finitePhysicalSynthesis
    (fun a => limitBlock hc M (Fin.castLE (Nat.add_le_add_right h 1) a)) x),
      norm_nonneg (finitePhysicalSynthesis (limitBlock hc N) x)]

abbrev LimitPhysicalRange (hc : AllFiniteReturnBounds) (N : ℕ) :=
  (finitePhysicalSynthesis (limitBlock hc N)).range

def limitTransition (hc : AllFiniteReturnBounds) {N M : ℕ} (h : N ≤ M) :
    LimitPhysicalRange hc N →ₗᵢ[ℂ] LimitPhysicalRange hc M := by
  let f := finitePhysicalSynthesis (limitBlock hc N)
  let g := finitePhysicalSynthesis
    (fun a => limitBlock hc M (Fin.castLE (Nat.add_le_add_right h 1) a))
  have hn : ∀ x, ‖g x‖ = ‖f x‖ := limitBlock_prefix_norm hc h
  let L := rangeTransportLinear f g hn
  have hm (z : f.range) : L z ∈ LimitPhysicalRange hc M := by
    obtain ⟨x,hx⟩ := z.property
    have hz : (⟨f x,⟨x,rfl⟩⟩ : f.range) = z := Subtype.ext hx
    rw [← hz, rangeTransportLinear_source]
    exact ⟨radialSourcePad (Nat.add_le_add_right h 1) x, finitePhysicalSynthesis_pad _ _ _⟩
  refine ⟨L.codRestrict _ hm, ?_⟩
  intro z
  obtain ⟨x,hx⟩ := z.property
  have hz : (⟨f x,⟨x,rfl⟩⟩ : f.range) = z := Subtype.ext hx
  rw [← hz]
  change ‖L ⟨f x,⟨x,rfl⟩⟩‖ = ‖f x‖
  rw [rangeTransportLinear_source]
  exact hn x

theorem limitTransition_source (hc : AllFiniteReturnBounds) {N M : ℕ} (h : N ≤ M)
    (x : Fin (N+1) → ℂ) :
    (limitTransition hc h ⟨finitePhysicalSynthesis (limitBlock hc N) x,⟨x,rfl⟩⟩ :
      CanonicalCompletedNativeChiralCauchyCarrier) =
      finitePhysicalSynthesis (limitBlock hc M) (radialSourcePad (Nat.add_le_add_right h 1) x) := by
  rw [finitePhysicalSynthesis_pad]
  exact rangeTransportLinear_source _ _ _ x

/-- The literal source-padding cocycle, before limit isometries are used. -/
theorem sourcePad_trans {N M L : ℕ} (hNM : N ≤ M) (hML : M ≤ L) (x : Fin N → ℂ) :
    radialSourcePad hML (radialSourcePad hNM x) = radialSourcePad (hNM.trans hML) x := by
  apply (radialIncidentSynthesis_injective 0 L)
  rw [radialIncidentSynthesis_pad, radialIncidentSynthesis_pad, radialIncidentSynthesis_pad]

theorem limitTransition_trans (hc : AllFiniteReturnBounds) {N M L : ℕ}
    (hNM : N ≤ M) (hML : M ≤ L) (z : LimitPhysicalRange hc N) :
    limitTransition hc hML (limitTransition hc hNM z) = limitTransition hc (hNM.trans hML) z := by
  obtain ⟨x,hx⟩ := z.property
  have hz : (⟨finitePhysicalSynthesis (limitBlock hc N) x,⟨x,rfl⟩⟩ : LimitPhysicalRange hc N) = z :=
    Subtype.ext hx
  rw [← hz]
  apply Subtype.ext
  have he : limitTransition hc hNM ⟨finitePhysicalSynthesis (limitBlock hc N) x,⟨x,rfl⟩⟩ =
      (⟨finitePhysicalSynthesis (limitBlock hc M) (radialSourcePad (Nat.add_le_add_right hNM 1) x),
        ⟨radialSourcePad (Nat.add_le_add_right hNM 1) x,rfl⟩⟩ : LimitPhysicalRange hc M) :=
    Subtype.ext (limitTransition_source hc hNM x)
  rw [he, limitTransition_source, limitTransition_source, sourcePad_trans]

theorem limitTransition_self (hc : AllFiniteReturnBounds) (N : ℕ)
    (z : LimitPhysicalRange hc N) : limitTransition hc (le_refl N) z = z := by
  obtain ⟨x,hx⟩ := z.property
  have hz : (⟨finitePhysicalSynthesis (limitBlock hc N) x,⟨x,rfl⟩⟩ : LimitPhysicalRange hc N) = z :=
    Subtype.ext hx
  rw [← hz]
  apply Subtype.ext
  rw [limitTransition_source, finitePhysicalSynthesis_pad]
  rfl

/-- Every column is transported by its SOURCE coefficient, independently
of choices of ambient representatives made by finite compactness. -/
theorem limitTransition_column (hc : AllFiniteReturnBounds) {N M : ℕ} (h : N ≤ M)
    (a : Fin (N+1)) :
    (limitTransition hc h
      ⟨finitePhysicalSynthesis (limitBlock hc N) (Pi.single a 1),⟨Pi.single a 1,rfl⟩⟩ :
        CanonicalCompletedNativeChiralCauchyCarrier) =
      limitBlock hc M (Fin.castLE (Nat.add_le_add_right h 1) a) := by
  rw [limitTransition_source, finitePhysicalSynthesis_pad]
  simp [finitePhysicalSynthesis]

/-- Source-facing sufficient estimate already isolated upstream. Its signs
remain open in general; this theorem does not infer them from compatibility. -/
theorem allFiniteReturnBounds_of_source_remainders
    (hR : ∀ n, 0 < nativeSourceSchurRemainder 0 n ∧ 0 < nativeSourceSchurRemainder 1 n) :
    AllFiniteReturnBounds := by
  intro N
  exact radialReturnTransfer_all_orders_of_sourceSchur hR (N+1)

end
end CarryReturnCompatibility
