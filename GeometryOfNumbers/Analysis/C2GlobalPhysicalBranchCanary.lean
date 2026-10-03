import GeometryOfNumbers.Analysis.C2PhysicalBranchCanary
import GeometryOfNumbers.Analysis.PrimeResidualDepthCrosswalk
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Global odd-material C2 physical branch source

Downstream of the fixed-core physical isometry. The explicit inverse reads the
neighbor divisible by four, then uses the already-proved residual-depth /
factorization crosswalk. No choice selects an address. Amplitude reads recovered
branch depth; the logarithmic phase reads the material integer.
-/
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis
noncomputable section

abbrev PositiveOddCore := {m : ℕ // 0 < m ∧ Odd m}
abbrev GlobalC2BranchAddress := PositiveOddCore × C2BranchAddress
abbrev OddMaterialIndex := {n : PNat // Odd (n : ℕ) ∧ 3 ≤ (n : ℕ)}

def globalC2MaterialAddress (i : GlobalC2BranchAddress) : PNat :=
  c2BranchMaterialAddress i.1.val i.1.property.1 i.2

theorem globalC2MaterialAddress_odd (i : GlobalC2BranchAddress) :
    Odd (globalC2MaterialAddress i : ℕ) := by
  have h := c2BranchMaterialNat_sign_mod_four i.1.val i.1.property.1 i.2
  change Odd (c2BranchMaterialNat i.1.val i.2)
  rw [Nat.odd_iff]
  split at h <;> omega

def globalC2OddMaterialAddress (i : GlobalC2BranchAddress) : OddMaterialIndex :=
  ⟨globalC2MaterialAddress i, globalC2MaterialAddress_odd i,
    c2BranchMaterialNat_ge_three i.1.val i.1.property.1 i.2⟩

theorem globalC2MaterialAddress_injective : Function.Injective globalC2MaterialAddress := by
  rintro ⟨m,i⟩ ⟨m',i'⟩ h
  have hn : c2BranchMaterialNat m.val i = c2BranchMaterialNat m'.val i' :=
    congrArg PNat.val h
  have hi := c2BranchMaterialAddress_depth_recovery m.val m.property.1 m.property.2 i
  have hi' := c2BranchMaterialAddress_depth_recovery m'.val m'.property.1 m'.property.2 i'
  have hd : c2BranchDepth i = c2BranchDepth i' := by
    apply Nat.le_antisymm
    · exact (hi' _).mp (hn ▸ (hi _).mpr le_rfl)
    · exact (hi _).mp (hn ▸ (hi' _).mpr le_rfl)
  have hmod := congrArg (fun n : ℕ => n % 4) hn
  rw [c2BranchMaterialNat_sign_mod_four m.val m.property.1,
    c2BranchMaterialNat_sign_mod_four m'.val m'.property.1] at hmod
  have hs : i.1 = i'.1 := by
    rcases i with ⟨a,j⟩; rcases i' with ⟨b,l⟩
    fin_cases a <;> fin_cases b <;> norm_num at *
  have he : i = i' := by
    apply Prod.ext hs
    unfold c2BranchDepth at hd
    omega
  subst i'
  have hc := c2BranchMaterialNat_core_recovery m.val m.property.1 i
  have hc' := c2BranchMaterialNat_core_recovery m'.val m'.property.1 i
  rw [hn] at hc
  have hm : m = m' := Subtype.ext (hc.symm.trans hc')
  subst m'
  rfl

/-- The selected neighboring center is determined by the material residue. -/
def oddMaterialNeighborCenter (n : OddMaterialIndex) : ℕ :=
  if (n.val : ℕ) % 4 = 3 then (n.val : ℕ) + 1 else (n.val : ℕ) - 1

private theorem odd_mod_four (n : OddMaterialIndex) :
    (n.val : ℕ) % 4 = 3 ∨ (n.val : ℕ) % 4 = 1 := by
  have h := (Nat.odd_iff.mp n.property.1)
  omega

private theorem neighbor_positive (n : OddMaterialIndex) : 0 < oddMaterialNeighborCenter n := by
  have h := n.property.2
  unfold oddMaterialNeighborCenter
  split <;> omega

private theorem neighbor_four (n : OddMaterialIndex) : 4 ∣ oddMaterialNeighborCenter n := by
  rcases odd_mod_four n with h | h
  · simp only [oddMaterialNeighborCenter, h, if_true]
    apply Nat.dvd_of_mod_eq_zero
    omega
  · have hn : (n.val : ℕ) % 4 ≠ 3 := by omega
    simp only [oddMaterialNeighborCenter, hn, if_false]
    apply Nat.dvd_of_mod_eq_zero
    have hg := n.property.2
    omega

/-- This exponent is a representation of the existing relational depth,
not a new definition of carry depth. -/
theorem oddMaterialNeighbor_depth_crosswalk (n : OddMaterialIndex) (r : ℕ) :
    Geometry.HasCarryDepthAtLeast 2 (oddMaterialNeighborCenter n) r ↔
      r ≤ (oddMaterialNeighborCenter n).factorization 2 :=
  primeResidualDepth_iff_le_factorization (by norm_num) (ne_of_gt (neighbor_positive n))

private theorem neighbor_depth_ge_two (n : OddMaterialIndex) :
    2 ≤ (oddMaterialNeighborCenter n).factorization 2 := by
  apply (oddMaterialNeighbor_depth_crosswalk n 2).mp
  apply (Geometry.hasCarryDepthAtLeast_iff_dvd_pow 2 _ 2 (by decide)).mpr
  simpa using neighbor_four n

private theorem neighbor_core_odd (n : OddMaterialIndex) :
    Odd (oddMaterialNeighborCenter n / 2 ^ (oddMaterialNeighborCenter n).factorization 2) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  exact Nat.not_dvd_ordCompl (by norm_num) (ne_of_gt (neighbor_positive n))

/-- Explicit arithmetic decoder; no `Classical.choose` or arbitrary enumeration. -/
def oddMaterialC2Address (n : OddMaterialIndex) : GlobalC2BranchAddress :=
  (⟨oddMaterialNeighborCenter n / 2 ^ (oddMaterialNeighborCenter n).factorization 2,
    Nat.ordCompl_pos 2 (ne_of_gt (neighbor_positive n)), neighbor_core_odd n⟩,
   (if (n.val : ℕ) % 4 = 3 then 0 else 1),
   (oddMaterialNeighborCenter n).factorization 2 - 2)

theorem oddMaterialC2Address_depth (n : OddMaterialIndex) :
    c2BranchDepth (oddMaterialC2Address n).2 =
      (oddMaterialNeighborCenter n).factorization 2 := by
  exact Nat.sub_add_cancel (neighbor_depth_ge_two n)

theorem globalC2MaterialAddress_decode (n : OddMaterialIndex) :
    globalC2MaterialAddress (oddMaterialC2Address n) = n.val := by
  apply PNat.eq
  change c2BranchMaterialNat (oddMaterialC2Address n).1.val (oddMaterialC2Address n).2 = _
  rw [c2BranchMaterialNat, oddMaterialC2Address_depth]
  have hc := Nat.ordProj_mul_ordCompl_eq_self (oddMaterialNeighborCenter n) 2
  change 2 ^ (oddMaterialNeighborCenter n).factorization 2 *
    (oddMaterialC2Address n).1.val = oddMaterialNeighborCenter n at hc
  rw [hc]
  by_cases h : (n.val : ℕ) % 4 = 3
  · simp [oddMaterialC2Address, h, oddMaterialNeighborCenter]
  · have hg := n.property.2
    simp only [oddMaterialC2Address, h, if_false, one_ne_zero, oddMaterialNeighborCenter]
    omega

theorem oddMaterialC2Address_encode (i : GlobalC2BranchAddress) :
    oddMaterialC2Address (globalC2OddMaterialAddress i) = i := by
  apply globalC2MaterialAddress_injective
  exact globalC2MaterialAddress_decode _

def globalC2BranchAddressEquivOddMaterial : GlobalC2BranchAddress ≃ OddMaterialIndex where
  toFun := globalC2OddMaterialAddress
  invFun := oddMaterialC2Address
  left_inv := oddMaterialC2Address_encode
  right_inv n := Subtype.ext (globalC2MaterialAddress_decode n)

theorem globalC2MaterialAddress_unique (n : OddMaterialIndex) :
    ∃! i : GlobalC2BranchAddress, globalC2MaterialAddress i = n.val :=
  ⟨oddMaterialC2Address n, globalC2MaterialAddress_decode n,
    fun _ hi => globalC2MaterialAddress_injective (hi.trans (globalC2MaterialAddress_decode n).symm)⟩

abbrev GlobalC2BranchCarrier := ℓ²(GlobalC2BranchAddress, RealPlaneHilbert)
abbrev OddMaterialState := ℓ²(OddMaterialIndex, RealPlaneHilbert)
abbrev CoreState := ℓ²(PositiveOddCore, RealPlaneHilbert)

private def reindexElement {α β : Type} (e : α ≃ β)
    (x : ℓ²(α, RealPlaneHilbert)) : ℓ²(β, RealPlaneHilbert) :=
  ⟨fun n => x (e.symm n), by
    change Memℓp (fun n => x (e.symm n)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact e.symm.summable_iff.mpr ((lp.memℓp x).summable (by norm_num))⟩

private def reindexLinearEquiv {α β : Type} (e : α ≃ β) :
    ℓ²(α, RealPlaneHilbert) ≃ₗ[ℝ] ℓ²(β, RealPlaneHilbert) where
  toFun := reindexElement e
  invFun := reindexElement e.symm
  left_inv x := by ext n r; simp [reindexElement]
  right_inv x := by ext n r; simp [reindexElement]
  map_add' x y := by ext n r; rfl
  map_smul' c x := by ext n r; rfl

private theorem reindexElement_norm {α β : Type} (e : α ≃ β)
    (x : ℓ²(α, RealPlaneHilbert)) : ‖reindexElement e x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hx := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  have hy := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (reindexElement e x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  rw [hy, hx]
  exact e.symm.tsum_eq (fun n => ‖x n‖ ^ 2)

/-- Bijection of indices, hence a surjective linear isometric reindexing. -/
def globalBranchIncidenceIsometry : GlobalC2BranchCarrier ≃ₗᵢ[ℝ] OddMaterialState :=
  { reindexLinearEquiv globalC2BranchAddressEquivOddMaterial with
    norm_map' := reindexElement_norm globalC2BranchAddressEquivOddMaterial }

theorem globalBranchIncidenceIsometry_apply_address (x : GlobalC2BranchCarrier)
    (i : GlobalC2BranchAddress) :
    globalBranchIncidenceIsometry x (globalC2OddMaterialAddress i) = x i := by
  change x (oddMaterialC2Address (globalC2OddMaterialAddress i)) = x i
  rw [oddMaterialC2Address_encode]

theorem globalBranchIncidenceIsometry_norm (x : GlobalC2BranchCarrier) :
    ‖globalBranchIncidenceIsometry x‖ = ‖x‖ :=
  globalBranchIncidenceIsometry.norm_map x

/-- The existing local physical isometry, before its material incidence. -/
def criticalPhysicalCoreFiber (m : PositiveOddCore) (t : ℝ) :
    RealPlaneHilbert →ₗᵢ[ℝ] C2BranchCarrier :=
  (physicalLegCorrection m.val t).comp (realCriticalBranchIsometry t)

theorem criticalPhysicalCoreFiber_eq_local_physical (m : PositiveOddCore) (t : ℝ)
    (v : RealPlaneHilbert) (i : C2BranchAddress) :
    criticalPhysicalCoreFiber m t v i =
      realCriticalPhysicalBranchIsometry m.val m.property.1 t v
        (c2BranchMaterialAddress m.val m.property.1 i) := by
  exact (branchIncidenceIsometry_apply_address m.val m.property.1 _ i).symm

private theorem fiber_square_sum (m : PositiveOddCore) (t : ℝ) (v : RealPlaneHilbert) :
    (∑' i : C2BranchAddress, ‖criticalPhysicalCoreFiber m t v i‖ ^ 2) = ‖v‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (criticalPhysicalCoreFiber m t v)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometry.norm_map] at h
  exact h.symm

private theorem fiber_summable (m : PositiveOddCore) (t : ℝ) (v : RealPlaneHilbert) :
    Summable (fun i : C2BranchAddress => ‖criticalPhysicalCoreFiber m t v i‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp (criticalPhysicalCoreFiber m t v)).summable (by norm_num)

private theorem core_summable (v : CoreState) : Summable (fun m => ‖v m‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.memℓp v).summable (by norm_num)

private theorem global_summable (t : ℝ) (v : CoreState) :
    Summable (fun i : GlobalC2BranchAddress => ‖criticalPhysicalCoreFiber i.1 t (v i.1) i.2‖ ^ 2) := by
  apply (summable_prod_of_nonneg (fun i => sq_nonneg _)).mpr
  constructor
  · exact fun m => fiber_summable m t (v m)
  · simpa only [fiber_square_sum] using core_summable v

private def globalBranchElement (t : ℝ) (v : CoreState) : GlobalC2BranchCarrier :=
  ⟨fun i : GlobalC2BranchAddress => criticalPhysicalCoreFiber i.1 t (v i.1) i.2, by
    change Memℓp (fun i : GlobalC2BranchAddress => criticalPhysicalCoreFiber i.1 t (v i.1) i.2) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using global_summable t v⟩

private def globalBranchLinear (t : ℝ) : CoreState →ₗ[ℝ] GlobalC2BranchCarrier where
  toFun := globalBranchElement t
  map_add' v w := by
    ext i r
    change criticalPhysicalCoreFiber i.1 t (v i.1 + w i.1) i.2 r = _
    simp [map_add, globalBranchElement]
  map_smul' c v := by
    ext i r
    change criticalPhysicalCoreFiber i.1 t (c • v i.1) i.2 r = _
    simp [map_smul, globalBranchElement]

private theorem globalBranchElement_norm (t : ℝ) (v : CoreState) :
    ‖globalBranchElement t v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hx := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v
  have hy := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (globalBranchElement t v)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  rw [hy, hx]
  change (∑' i : GlobalC2BranchAddress,
    ‖criticalPhysicalCoreFiber i.1 t (v i.1) i.2‖ ^ 2) = _
  rw [(global_summable t v).tsum_prod' (fun m => fiber_summable m t (v m))]
  simp only [fiber_square_sum]

/-- Orthogonal Hilbert sum of the previously constructed local fibers. -/
def globalCriticalPhysicalBranch (t : ℝ) : CoreState →ₗᵢ[ℝ] GlobalC2BranchCarrier :=
  { globalBranchLinear t with norm_map' := globalBranchElement_norm t }

def globalCriticalPhysicalBranchIsometry (t : ℝ) : CoreState →ₗᵢ[ℝ] OddMaterialState :=
  globalBranchIncidenceIsometry.toLinearIsometry.comp (globalCriticalPhysicalBranch t)

theorem globalCriticalPhysicalBranchIsometry_norm (t : ℝ) (v : CoreState) :
    ‖globalCriticalPhysicalBranchIsometry t v‖ = ‖v‖ :=
  (globalCriticalPhysicalBranchIsometry t).norm_map v

theorem globalCriticalPhysicalBranchIsometry_norm_sq (t : ℝ) (v : CoreState) :
    ‖globalCriticalPhysicalBranchIsometry t v‖ ^ 2 = ∑' m : PositiveOddCore, ‖v m‖ ^ 2 := by
  rw [globalCriticalPhysicalBranchIsometry_norm]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) v

theorem globalCriticalPhysicalBranchIsometry_apply_address (t : ℝ) (v : CoreState)
    (i : GlobalC2BranchAddress) :
    globalCriticalPhysicalBranchIsometry t v (globalC2OddMaterialAddress i) =
      realCriticalPhysicalBranchIsometry i.1.val i.1.property.1 t (v i.1)
        (globalC2MaterialAddress i) := by
  change globalBranchIncidenceIsometry (globalCriticalPhysicalBranch t v)
    (globalC2OddMaterialAddress i) = _
  rw [globalBranchIncidenceIsometry_apply_address]
  exact criticalPhysicalCoreFiber_eq_local_physical i.1 t (v i.1) i.2

theorem globalCriticalPhysicalBranchIsometry_pointwise (t : ℝ) (v : CoreState)
    (n : OddMaterialIndex) :
    realPlaneHilbertEquiv.symm (globalCriticalPhysicalBranchIsometry t v n) =
      scaleRealPlane ((2 : ℝ) ^ (-(c2BranchDepth (oddMaterialC2Address n).2 : ℝ) / 2))
        (rotateRealPlane (-t * Real.log ((n.val : ℕ) : ℝ))
          (realPlaneHilbertEquiv.symm (v (oddMaterialC2Address n).1))) := by
  have he : globalC2OddMaterialAddress (oddMaterialC2Address n) = n :=
    globalC2BranchAddressEquivOddMaterial.apply_symm_apply n
  rw [← he, globalCriticalPhysicalBranchIsometry_apply_address]
  change realPlaneHilbertEquiv.symm
    (physicalBranchOperator ((1 : ℝ) / 2) t (by norm_num)
      (oddMaterialC2Address n).1.val (oddMaterialC2Address n).1.property.1
      (v (oddMaterialC2Address n).1)
      (c2BranchMaterialAddress _ _ (oddMaterialC2Address n).2)) = _
  rw [physicalBranchOperator_apply_address, oddMaterialC2Address_encode]
  congr 2
  ring

/-- Distinct cores occupy disjoint material subsets, regardless of vector values. -/
theorem physicalBranch_support_disjoint_of_core_ne (m l : PositiveOddCore) (h : m ≠ l) :
    Disjoint (Set.range (c2BranchMaterialAddress m.val m.property.1))
      (Set.range (c2BranchMaterialAddress l.val l.property.1)) := by
  rw [Set.disjoint_left]
  rintro n ⟨i,hi⟩ ⟨j,hj⟩
  have he : globalC2MaterialAddress (m,i) = globalC2MaterialAddress (l,j) := hi.trans hj.symm
  exact h (congrArg Prod.fst (globalC2MaterialAddress_injective he))

theorem globalCriticalPhysicalBranch_core_orthogonal (t : ℝ) (m l : PositiveOddCore)
    (h : m ≠ l) (v w : RealPlaneHilbert) :
    inner ℝ (globalCriticalPhysicalBranchIsometry t (lp.single 2 m v))
      (globalCriticalPhysicalBranchIsometry t (lp.single 2 l w)) = 0 := by
  classical
  rw [(globalCriticalPhysicalBranchIsometry t).inner_map_map, lp.inner_single_left]
  simp [lp.single_apply, Pi.single_eq_of_ne h]

/-- Provenance is recovered on every index, even when its vector is zero. -/
theorem globalC2_provenance_roundtrip (n : OddMaterialIndex) :
    globalC2OddMaterialAddress (oddMaterialC2Address n) = n ∧
    c2BranchDepth (oddMaterialC2Address n).2 =
      (oddMaterialNeighborCenter n).factorization 2 ∧
    (∀ r, C2LegHasCarryDepthAtLeast (n.val : ℕ) r ↔
      r ≤ c2BranchDepth (oddMaterialC2Address n).2) := by
  refine ⟨globalC2BranchAddressEquivOddMaterial.apply_symm_apply n,
    oddMaterialC2Address_depth n, ?_⟩
  intro r
  have h := c2BranchMaterialAddress_depth_recovery (oddMaterialC2Address n).1.val
    (oddMaterialC2Address n).1.property.1 (oddMaterialC2Address n).1.property.2
    (oddMaterialC2Address n).2 r
  have hn := congrArg PNat.val (globalC2MaterialAddress_decode n)
  change c2BranchMaterialNat _ _ = (n.val : ℕ) at hn
  rwa [hn] at h

/-- The three address fields round-trip independently. -/
theorem globalC2Address_components_roundtrip (i : GlobalC2BranchAddress) :
    (oddMaterialC2Address (globalC2OddMaterialAddress i)).1 = i.1 ∧
    (oddMaterialC2Address (globalC2OddMaterialAddress i)).2.1 = i.2.1 ∧
    c2BranchDepth (oddMaterialC2Address (globalC2OddMaterialAddress i)).2 = c2BranchDepth i.2 := by
  rw [oddMaterialC2Address_encode]
  exact ⟨rfl,rfl,rfl⟩

theorem oddMaterialC2Address_sign (n : OddMaterialIndex) :
    (oddMaterialC2Address n).2.1 = if (n.val : ℕ) % 4 = 3 then 0 else 1 := rfl

theorem oddMaterialC2Address_core (n : OddMaterialIndex) :
    (oddMaterialC2Address n).1.val =
      oddMaterialNeighborCenter n / 2 ^ (oddMaterialNeighborCenter n).factorization 2 := rfl

/-- The single-core global source agrees with the old local physical source
at every material index in the odd sector, including coordinates off support. -/
theorem globalCriticalPhysicalBranch_single_core (t : ℝ) (m : PositiveOddCore)
    (v : RealPlaneHilbert) (n : OddMaterialIndex) :
    globalCriticalPhysicalBranchIsometry t (lp.single 2 m v) n =
      realCriticalPhysicalBranchIsometry m.val m.property.1 t v n.val := by
  classical
  let i := oddMaterialC2Address n
  have hn : globalC2OddMaterialAddress i = n :=
    globalC2BranchAddressEquivOddMaterial.apply_symm_apply n
  rw [← hn, globalCriticalPhysicalBranchIsometry_apply_address]
  by_cases hm : i.1 = m
  · simp only [hm, lp.single_apply, Pi.single_eq_same]
    rfl
  · have hz : (lp.single 2 m v : CoreState) i.1 = 0 := by
      simp [lp.single_apply, Pi.single_eq_of_ne hm]
    rw [hz, map_zero]
    have hr : globalC2MaterialAddress i ∉ Set.range (c2BranchMaterialAddress m.val m.property.1) := by
      rintro ⟨j,hj⟩
      have he : globalC2MaterialAddress (m,j) = globalC2MaterialAddress i := hj
      exact hm (congrArg Prod.fst (globalC2MaterialAddress_injective he)).symm
    exact (physicalBranchOperator_apply_off_range ((1 : ℝ) / 2) t (by norm_num)
      m.val m.property.1 v _ hr).symm

/-- A vector source coordinate can only originate in its decoded core. -/
theorem globalCriticalPhysicalBranch_zero_of_core_zero (t : ℝ) (v : CoreState)
    (n : OddMaterialIndex) (h : v (oddMaterialC2Address n).1 = 0) :
    globalCriticalPhysicalBranchIsometry t v n = 0 := by
  have hn : globalC2OddMaterialAddress (oddMaterialC2Address n) = n :=
    globalC2BranchAddressEquivOddMaterial.apply_symm_apply n
  rw [← hn, globalCriticalPhysicalBranchIsometry_apply_address, h, map_zero]
  rfl

end
end GeometryOfNumbers.Analysis
