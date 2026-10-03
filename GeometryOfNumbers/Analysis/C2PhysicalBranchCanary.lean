import GeometryOfNumbers.Analysis.C2BranchIsometryCanary
import Mathlib.Data.PNat.Basic

/-!
# Physical C2 material incidence and exact leg-phase correction

Historical reference, read only: formalizacao_C2/LeanC2/Foundations/Dyadic.lean,
commit dc35555879e3c0f188508c729c4a0ea31be246fb, working-content SHA256
a7b17be4ee2a41064886ef4179495aa229c3ee73da8e5028f382e9a717944c98.
The historical file is dirty; its declarations are not proof dependencies.

Depth j+2 and sign retain their branch roles. The material integer is their
derived address, not the depth. Incidence alone does not make the pure branch
phase physical. A separate coordinatewise rotation retains the exact leg
log-defect. No historical diagonal source is reconstructed.
-/

open scoped BigOperators lp ENNReal

namespace GeometryOfNumbers.Analysis
noncomputable section

abbrev C2BranchAddress := C2BranchDirection × ℕ
abbrev RealMaterialState := ℓ²(PNat, RealPlaneHilbert)

def c2BranchDepth (i : C2BranchAddress) : ℕ := i.2 + 2

def c2BranchMaterialNat (m : ℕ) (i : C2BranchAddress) : ℕ :=
  if i.1 = 0 then 2 ^ c2BranchDepth i * m - 1 else 2 ^ c2BranchDepth i * m + 1

private theorem center_four (m j : ℕ) : 2 ^ (j + 2) * m = 4 * (2 ^ j * m) := by
  rw [pow_add]
  norm_num
  ring

theorem c2BranchMaterialNat_ge_three (m : ℕ) (hm : 0 < m) (i : C2BranchAddress) :
    3 ≤ c2BranchMaterialNat m i := by
  have hp : 0 < 2 ^ i.2 * m := by positivity
  rw [c2BranchMaterialNat, c2BranchDepth, center_four]
  split <;> omega

def c2BranchMaterialAddress (m : ℕ) (hm : 0 < m) (i : C2BranchAddress) : PNat :=
  ⟨c2BranchMaterialNat m i, by have h := c2BranchMaterialNat_ge_three m hm i; omega⟩

theorem c2BranchMaterialNat_sign_mod_four (m : ℕ) (hm : 0 < m) (i : C2BranchAddress) :
    c2BranchMaterialNat m i % 4 = if i.1 = 0 then 3 else 1 := by
  have hp : 0 < 2 ^ i.2 * m := by positivity
  rw [c2BranchMaterialNat, c2BranchDepth, center_four]
  split <;> omega

theorem c2BranchMaterialAddress_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (c2BranchMaterialAddress m hm) := by
  rintro ⟨a,j⟩ ⟨b,l⟩ h
  have hn : c2BranchMaterialNat m (a,j) = c2BranchMaterialNat m (b,l) :=
    congrArg PNat.val h
  have hmod := congrArg (fun n : ℕ => n % 4) hn
  rw [c2BranchMaterialNat_sign_mod_four m hm,
    c2BranchMaterialNat_sign_mod_four m hm] at hmod
  have hab : a = b := by fin_cases a <;> fin_cases b <;> norm_num at *
  subst b
  have hc : 2 ^ (j + 2) * m = 2 ^ (l + 2) * m := by
    have hj : 0 < 2 ^ (j + 2) * m := by positivity
    have hl : 0 < 2 ^ (l + 2) * m := by positivity
    simp only [c2BranchMaterialNat, c2BranchDepth] at hn
    split at hn <;> omega
  have hpow := mul_right_cancel₀ (by omega : m ≠ 0) hc
  have hd := Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) hpow
  have hjl : j = l := by omega
  subst l
  rfl

theorem c2BranchMaterialAddress_eq_iff (m : ℕ) (hm : 0 < m) (i l : C2BranchAddress) :
    c2BranchMaterialAddress m hm i = c2BranchMaterialAddress m hm l ↔ i = l :=
  (c2BranchMaterialAddress_injective m hm).eq_iff

theorem c2BranchMaterialNat_core_recovery (m : ℕ) (hm : 0 < m) (i : C2BranchAddress) :
    (if i.1 = 0 then c2BranchMaterialNat m i + 1 else c2BranchMaterialNat m i - 1) /
      2 ^ c2BranchDepth i = m := by
  have hp : 0 < 2 ^ c2BranchDepth i * m := by positivity
  have he : (if i.1 = 0 then c2BranchMaterialNat m i + 1
      else c2BranchMaterialNat m i - 1) = 2 ^ c2BranchDepth i * m := by
    by_cases ha : i.1 = 0
    · simpa only [c2BranchMaterialNat, ha, if_true] using
        Nat.sub_add_cancel (Nat.succ_le_of_lt hp)
    · simp [c2BranchMaterialNat, ha]
  rw [he, Nat.mul_div_right _ (by positivity)]

/-- Effective leg depth reads its neighboring centers, not the odd leg itself. -/
def C2LegHasCarryDepthAtLeast (n r : ℕ) : Prop :=
  Geometry.HasCarryDepthAtLeast 2 (n - 1) r ∨ Geometry.HasCarryDepthAtLeast 2 (n + 1) r

private theorem center_depth_iff (m k r : ℕ) (hm : Odd m) :
    Geometry.HasCarryDepthAtLeast 2 (2 ^ k * m) r ↔ r ≤ k := by
  rw [Geometry.hasCarryDepthAtLeast_iff_dvd_pow 2 _ _ (by decide)]
  constructor
  · intro h
    by_contra hn
    have hle : k + 1 ≤ r := by omega
    have hd : 2 ^ (k + 1) ∣ 2 ^ k * m := dvd_trans (pow_dvd_pow 2 hle) h
    exact c2FiberCenter_not_hasCarryDepthAtLeast_succ m k hm
      ((Geometry.hasCarryDepthAtLeast_iff_dvd_pow 2 _ _ (by decide)).mpr hd)
  · intro h
    exact dvd_trans (pow_dvd_pow 2 h) (dvd_mul_right _ _)

theorem c2BranchMaterialAddress_depth_recovery (m : ℕ) (hm : 0 < m) (hodd : Odd m)
    (i : C2BranchAddress) (r : ℕ) :
    C2LegHasCarryDepthAtLeast (c2BranchMaterialNat m i) r ↔ r ≤ c2BranchDepth i := by
  have hp : 0 < 2 ^ i.2 * m := by positivity
  have hc := center_four m i.2
  have hlarge : 4 ≤ 2 ^ c2BranchDepth i * m := by dsimp [c2BranchDepth]; omega
  have hleft : (2 ^ c2BranchDepth i * m - 1) + 1 = 2 ^ c2BranchDepth i * m := by omega
  have hright : (2 ^ c2BranchDepth i * m + 1) - 1 = 2 ^ c2BranchDepth i * m := by omega
  have hsmall (n : ℕ) (hn : n = 2 ^ c2BranchDepth i * m - 2 ∨
      n = 2 ^ c2BranchDepth i * m + 2)
      (h : Geometry.HasCarryDepthAtLeast 2 n r) : r ≤ c2BranchDepth i := by
    by_contra hnot
    have hr : 2 ≤ r := by dsimp [c2BranchDepth] at hnot; omega
    have hd : 4 ∣ n := by
      have hd := (Geometry.hasCarryDepthAtLeast_iff_dvd_pow 2 n r (by decide)).mp h
      exact dvd_trans (by simpa using pow_dvd_pow (2 : ℕ) hr) hd
    rcases hd with ⟨z,hz⟩
    dsimp [c2BranchDepth] at hn
    rcases hn with hn | hn <;> omega
  unfold c2BranchMaterialNat C2LegHasCarryDepthAtLeast
  split
  · rw [hleft]
    constructor
    · rintro (h | h)
      · apply hsmall _ (Or.inl (by omega)) h
      · exact (center_depth_iff m _ _ hodd).mp h
    · intro h
      exact Or.inr ((center_depth_iff m _ _ hodd).mpr h)
  · rw [hright]
    constructor
    · rintro (h | h)
      · exact (center_depth_iff m _ _ hodd).mp h
      · apply hsmall _ (Or.inr (by omega)) h
    · intro h
      exact Or.inl ((center_depth_iff m _ _ hodd).mpr h)

theorem c2BranchMaterialAddress_cast_eq_fiberPoint (m : ℕ) (hm : 0 < m)
    (i : C2BranchAddress) :
    ((c2BranchMaterialAddress m hm i : ℕ) : ℝ) =
      c2FiberPoint m (c2BranchDirectionSign i.1 : ℝ) (c2BranchDepth i) := by
  rcases i with ⟨a,j⟩
  fin_cases a
  · simp [c2BranchMaterialAddress, c2BranchMaterialNat,
      c2BranchDirectionSign, c2FiberPoint, c2BranchDepth]
    rw [Nat.cast_sub (Nat.succ_le_of_lt (by positivity : 0 < 2 ^ (j + 2) * m))]
    push_cast
    ring
  · simp [c2BranchMaterialAddress, c2BranchMaterialNat,
      c2BranchDirectionSign, c2FiberPoint, c2BranchDepth]

private theorem fiber_pos (m : ℕ) (hm : 0 < m) (i : C2BranchAddress) :
    0 < c2FiberPoint m (c2BranchDirectionSign i.1 : ℝ) (c2BranchDepth i) := by
  rw [← c2BranchMaterialAddress_cast_eq_fiberPoint m hm i]
  exact_mod_cast (c2BranchMaterialAddress m hm i).pos

def branchIncidenceCoordinates (m : ℕ) (hm : 0 < m) (x : C2BranchCarrier) :
    PNat → RealPlaneHilbert := Function.extend (c2BranchMaterialAddress m hm) x 0

private theorem incidence_norm_sq_extend (m : ℕ) (hm : 0 < m) (x : C2BranchCarrier) :
    (fun n => ‖branchIncidenceCoordinates m hm x n‖ ^ 2) =
      Function.extend (c2BranchMaterialAddress m hm) (fun i => ‖x i‖ ^ 2) 0 := by
  funext n
  by_cases h : ∃ i, c2BranchMaterialAddress m hm i = n
  · rcases h with ⟨i,rfl⟩
    simp [branchIncidenceCoordinates, (c2BranchMaterialAddress_injective m hm).extend_apply]
  · simp [branchIncidenceCoordinates, Function.extend_apply' _ _ _ h]

private def incidenceElement (m : ℕ) (hm : 0 < m) (x : C2BranchCarrier) : RealMaterialState :=
  ⟨branchIncidenceCoordinates m hm x, by
    change Memℓp (branchIncidenceCoordinates m hm x) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [incidence_norm_sq_extend]
    exact (summable_extend_zero (c2BranchMaterialAddress_injective m hm)).mpr
      (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩

private def incidenceLinear (m : ℕ) (hm : 0 < m) : C2BranchCarrier →ₗ[ℝ] RealMaterialState where
  toFun := incidenceElement m hm
  map_add' x y := by
    ext n r
    by_cases h : ∃ i, c2BranchMaterialAddress m hm i = n
    · rcases h with ⟨i,rfl⟩
      simp [incidenceElement, branchIncidenceCoordinates,
        (c2BranchMaterialAddress_injective m hm).extend_apply]
    · simp [incidenceElement, branchIncidenceCoordinates, Function.extend_apply' _ _ _ h]
  map_smul' c x := by
    ext n r
    by_cases h : ∃ i, c2BranchMaterialAddress m hm i = n
    · rcases h with ⟨i,rfl⟩
      simp [incidenceElement, branchIncidenceCoordinates,
        (c2BranchMaterialAddress_injective m hm).extend_apply]
    · simp [incidenceElement, branchIncidenceCoordinates, Function.extend_apply' _ _ _ h]

private theorem incidenceElement_norm (m : ℕ) (hm : 0 < m) (x : C2BranchCarrier) :
    ‖incidenceElement m hm x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hx := lp.norm_rpow_eq_tsum hp x
  have hy := lp.norm_rpow_eq_tsum hp (incidenceElement m hm x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  change ‖incidenceElement m hm x‖ ^ 2 =
    ∑' n : PNat, ‖branchIncidenceCoordinates m hm x n‖ ^ 2 at hy
  rw [hy, incidence_norm_sq_extend, tsum_extend_zero
    (c2BranchMaterialAddress_injective m hm)]
  exact hx.symm

def branchIncidenceIsometry (m : ℕ) (hm : 0 < m) :
    C2BranchCarrier →ₗᵢ[ℝ] RealMaterialState :=
  { incidenceLinear m hm with norm_map' := incidenceElement_norm m hm }

theorem branchIncidenceIsometry_apply_address (m : ℕ) (hm : 0 < m)
    (x : C2BranchCarrier) (i : C2BranchAddress) :
    branchIncidenceIsometry m hm x (c2BranchMaterialAddress m hm i) = x i :=
  (c2BranchMaterialAddress_injective m hm).extend_apply x 0 i

theorem branchIncidenceIsometry_apply_off_range (m : ℕ) (hm : 0 < m)
    (x : C2BranchCarrier) (n : PNat) (hn : n ∉ Set.range (c2BranchMaterialAddress m hm)) :
    branchIncidenceIsometry m hm x n = 0 :=
  Function.extend_apply' (x : C2BranchAddress → RealPlaneHilbert)
    (0 : PNat → RealPlaneHilbert) n hn

theorem branchIncidenceIsometry_norm (m : ℕ) (hm : 0 < m) (x : C2BranchCarrier) :
    ‖branchIncidenceIsometry m hm x‖ = ‖x‖ := (branchIncidenceIsometry m hm).norm_map x

theorem branchIncidenceIsometry_coordinate_roundtrip (m : ℕ) (hm : 0 < m)
    (x : C2BranchCarrier) :
    (fun i => branchIncidenceIsometry m hm x (c2BranchMaterialAddress m hm i)) =
      (x : C2BranchAddress → RealPlaneHilbert) := by
  funext i
  exact branchIncidenceIsometry_apply_address m hm x i

def c2PhysicalLegCorrectionAngle (m : ℕ) (t : ℝ) (i : C2BranchAddress) : ℝ :=
  -t * (Real.log m + c2FiberLogDefect m (c2BranchDirectionSign i.1 : ℝ) (c2BranchDepth i))

theorem c2PhysicalLegPhase_factorization (m : ℕ) (hm : 0 < m) (t : ℝ)
    (i : C2BranchAddress) (v : RealPlaneState) :
    rotateRealPlane (c2PhysicalLegCorrectionAngle m t i)
      (rotateRealPlane (-(c2BranchDepth i : ℝ) * t * Real.log 2) v) =
      rotateRealPlane (-t * Real.log ((c2BranchMaterialAddress m hm i : ℕ) : ℝ)) v := by
  rw [c2BranchMaterialAddress_cast_eq_fiberPoint,
    c2FiberPoint_log_eq_depth_core_defect m _ hm _ (fiber_pos m hm i),
    ← rotateRealPlane_add]
  congr 1
  unfold c2PhysicalLegCorrectionAngle
  ring

def realPlaneHilbertRotation (theta : ℝ) : RealPlaneHilbert →ₗᵢ[ℝ] RealPlaneHilbert where
  toFun v := realPlaneHilbertEquiv (rotateRealPlane theta (realPlaneHilbertEquiv.symm v))
  map_add' v w := by
    have h (a b : RealPlaneState) : rotateRealPlane theta (a + b) =
        rotateRealPlane theta a + rotateRealPlane theta b := by
      apply Prod.ext <;> simp [rotateRealPlane] <;> ring
    simp only [map_add, h]
  map_smul' c v := by
    have h (a : RealPlaneState) : rotateRealPlane theta (c • a) =
        c • rotateRealPlane theta a := by
      apply Prod.ext <;> simp [rotateRealPlane] <;> ring
    simp only [map_smul, h, RingHom.id_apply]
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖realPlaneHilbertEquiv (rotateRealPlane theta (realPlaneHilbertEquiv.symm v))‖ ^ 2 = ‖v‖ ^ 2
    rw [← realPlaneHilbert_energy_eq_norm_sq, LinearEquiv.symm_apply_apply,
      rotateRealPlane_energy, realPlaneHilbert_energy_eq_norm_sq]

theorem realPlaneHilbertRotation_neg_comp (theta : ℝ) (v : RealPlaneHilbert) :
    realPlaneHilbertRotation (-theta) (realPlaneHilbertRotation theta v) = v := by
  change realPlaneHilbertEquiv (rotateRealPlane (-theta)
    (realPlaneHilbertEquiv.symm (realPlaneHilbertEquiv
      (rotateRealPlane theta (realPlaneHilbertEquiv.symm v))))) = v
  rw [LinearEquiv.symm_apply_apply, ← rotateRealPlane_add, neg_add_cancel,
    rotateRealPlane_zero, LinearEquiv.apply_symm_apply]

private def correctionElement (m : ℕ) (t : ℝ) (x : C2BranchCarrier) : C2BranchCarrier :=
  ⟨fun i => realPlaneHilbertRotation (c2PhysicalLegCorrectionAngle m t i) (x i), by
    change Memℓp (fun i => realPlaneHilbertRotation (c2PhysicalLegCorrectionAngle m t i) (x i)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa only [LinearIsometry.norm_map] using
      (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)⟩

private def correctionLinear (m : ℕ) (t : ℝ) : C2BranchCarrier →ₗ[ℝ] C2BranchCarrier where
  toFun := correctionElement m t
  map_add' x y := by ext i r; simp [correctionElement, map_add]
  map_smul' c x := by ext i r; simp [correctionElement, map_smul]

private theorem correctionElement_norm (m : ℕ) (t : ℝ) (x : C2BranchCarrier) :
    ‖correctionElement m t x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hx := lp.norm_rpow_eq_tsum hp x
  have hy := lp.norm_rpow_eq_tsum hp (correctionElement m t x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  change ‖correctionElement m t x‖ ^ 2 =
    ∑' i : C2BranchAddress, ‖realPlaneHilbertRotation (c2PhysicalLegCorrectionAngle m t i) (x i)‖ ^ 2 at hy
  simp only [LinearIsometry.norm_map] at hy
  exact hy.trans hx.symm

def physicalLegCorrection (m : ℕ) (t : ℝ) : C2BranchCarrier →ₗᵢ[ℝ] C2BranchCarrier :=
  { correctionLinear m t with norm_map' := correctionElement_norm m t }

theorem physicalLegCorrection_apply (m : ℕ) (t : ℝ) (x : C2BranchCarrier)
    (i : C2BranchAddress) :
    physicalLegCorrection m t x i =
      realPlaneHilbertRotation (c2PhysicalLegCorrectionAngle m t i) (x i) := rfl

theorem physicalLegCorrection_norm (m : ℕ) (t : ℝ) (x : C2BranchCarrier) :
    ‖physicalLegCorrection m t x‖ = ‖x‖ := (physicalLegCorrection m t).norm_map x

theorem physicalLegCorrection_neg_comp (m : ℕ) (t : ℝ) (x : C2BranchCarrier) :
    physicalLegCorrection m (-t) (physicalLegCorrection m t x) = x := by
  have ha (i : C2BranchAddress) : c2PhysicalLegCorrectionAngle m (-t) i =
      -c2PhysicalLegCorrectionAngle m t i := by unfold c2PhysicalLegCorrectionAngle; ring
  ext i r
  simp only [physicalLegCorrection_apply, ha, realPlaneHilbertRotation_neg_comp]

def physicalBranchOperator (sigma t : ℝ) (hsigma : 0 < sigma) (m : ℕ) (hm : 0 < m) :
    RealPlaneHilbert →ₗ[ℝ] RealMaterialState :=
  (branchIncidenceIsometry m hm).toLinearMap.comp
    ((physicalLegCorrection m t).toLinearMap.comp (realBranchOperatorLinear sigma t hsigma))

private theorem rotate_scale (theta a : ℝ) (v : RealPlaneState) :
    rotateRealPlane theta (scaleRealPlane a v) = scaleRealPlane a (rotateRealPlane theta v) := by
  apply Prod.ext <;> simp [rotateRealPlane, scaleRealPlane] <;> ring

theorem physicalBranchOperator_apply_address (sigma t : ℝ) (hsigma : 0 < sigma)
    (m : ℕ) (hm : 0 < m) (v : RealPlaneHilbert) (i : C2BranchAddress) :
    realPlaneHilbertEquiv.symm
      (physicalBranchOperator sigma t hsigma m hm v (c2BranchMaterialAddress m hm i)) =
      scaleRealPlane ((2 : ℝ) ^ (-(c2BranchDepth i : ℝ) * sigma))
        (rotateRealPlane (-t * Real.log ((c2BranchMaterialAddress m hm i : ℕ) : ℝ))
          (realPlaneHilbertEquiv.symm v)) := by
  change realPlaneHilbertEquiv.symm (branchIncidenceIsometry m hm
    (physicalLegCorrection m t (realBranchOperator sigma t hsigma v))
      (c2BranchMaterialAddress m hm i)) = _
  rw [branchIncidenceIsometry_apply_address, physicalLegCorrection_apply]
  change rotateRealPlane (c2PhysicalLegCorrectionAngle m t i)
    (realPlaneHilbertEquiv.symm (realBranchOperator sigma t hsigma v i)) = _
  rw [realBranchOperator_apply_closed_form, rotate_scale]
  exact congrArg (scaleRealPlane ((2 : ℝ) ^ (-(c2BranchDepth i : ℝ) * sigma)))
    (c2PhysicalLegPhase_factorization m hm t i (realPlaneHilbertEquiv.symm v))

theorem physicalBranchOperator_apply_off_range (sigma t : ℝ) (hsigma : 0 < sigma)
    (m : ℕ) (hm : 0 < m) (v : RealPlaneHilbert) (n : PNat)
    (hn : n ∉ Set.range (c2BranchMaterialAddress m hm)) :
    physicalBranchOperator sigma t hsigma m hm v n = 0 :=
  branchIncidenceIsometry_apply_off_range m hm _ n hn

theorem physicalBranchOperator_norm (sigma t : ℝ) (hsigma : 0 < sigma)
    (m : ℕ) (hm : 0 < m) (v : RealPlaneHilbert) :
    ‖physicalBranchOperator sigma t hsigma m hm v‖ = ‖realBranchOperator sigma t hsigma v‖ := by
  change ‖branchIncidenceIsometry m hm
    (physicalLegCorrection m t (realBranchOperator sigma t hsigma v))‖ = _
  rw [branchIncidenceIsometry_norm, physicalLegCorrection_norm]

theorem physicalBranchOperator_norm_sq (sigma t : ℝ) (hsigma : 0 < sigma)
    (m : ℕ) (hm : 0 < m) (v : RealPlaneHilbert) :
    ‖physicalBranchOperator sigma t hsigma m hm v‖ ^ 2 =
      c2BranchOrbitMass sigma t * realPlaneEnergy (realPlaneHilbertEquiv.symm v) := by
  rw [physicalBranchOperator_norm, realBranchOperator_norm_sq]

def realCriticalPhysicalBranchIsometry (m : ℕ) (hm : 0 < m) (t : ℝ) :
    RealPlaneHilbert →ₗᵢ[ℝ] RealMaterialState :=
  (branchIncidenceIsometry m hm).comp
    ((physicalLegCorrection m t).comp (realCriticalBranchIsometry t))

theorem realCriticalPhysicalBranchIsometry_eq_operator (m : ℕ) (hm : 0 < m) (t : ℝ) :
    (realCriticalPhysicalBranchIsometry m hm t).toLinearMap =
      physicalBranchOperator ((1 : ℝ) / 2) t (by norm_num) m hm := rfl

theorem realCriticalPhysicalBranchIsometry_norm (m : ℕ) (hm : 0 < m) (t : ℝ)
    (v : RealPlaneHilbert) : ‖realCriticalPhysicalBranchIsometry m hm t v‖ = ‖v‖ :=
  (realCriticalPhysicalBranchIsometry m hm t).norm_map v

theorem realCriticalPhysicalBranch_adjoint_comp_self (m : ℕ) (hm : 0 < m) (t : ℝ) :
    (realCriticalPhysicalBranchIsometry m hm t).toContinuousLinearMap.adjoint ∘L
      (realCriticalPhysicalBranchIsometry m hm t).toContinuousLinearMap = 1 :=
  (realCriticalPhysicalBranchIsometry m hm t).adjoint_comp_self

theorem c2BranchMaterialAddress_range_unique (m : ℕ) (hm : 0 < m) (n : PNat)
    (hn : n ∈ Set.range (c2BranchMaterialAddress m hm)) :
    ∃! i : C2BranchAddress, c2BranchMaterialAddress m hm i = n := by
  rcases hn with ⟨i,rfl⟩
  exact ⟨i,rfl,fun l h => c2BranchMaterialAddress_injective m hm h⟩

theorem physicalBranchOperator_nonzero_provenance (sigma t : ℝ) (hsigma : 0 < sigma)
    (m : ℕ) (hm : 0 < m) (v : RealPlaneHilbert) (n : PNat)
    (hn : physicalBranchOperator sigma t hsigma m hm v n ≠ 0) :
    ∃! i : C2BranchAddress, c2BranchMaterialAddress m hm i = n := by
  apply c2BranchMaterialAddress_range_unique m hm n
  by_contra h
  exact hn (physicalBranchOperator_apply_off_range sigma t hsigma m hm v n h)

theorem physicalBranchOperator_branch_coordinate_roundtrip (sigma t : ℝ)
    (hsigma : 0 < sigma) (m : ℕ) (hm : 0 < m) (v : RealPlaneHilbert) :
    (fun i => realPlaneHilbertRotation (-c2PhysicalLegCorrectionAngle m t i)
      (physicalBranchOperator sigma t hsigma m hm v (c2BranchMaterialAddress m hm i))) =
      (realBranchOperator sigma t hsigma v : C2BranchAddress → RealPlaneHilbert) := by
  funext i
  change realPlaneHilbertRotation (-c2PhysicalLegCorrectionAngle m t i)
    (branchIncidenceIsometry m hm (physicalLegCorrection m t
      (realBranchOperator sigma t hsigma v)) (c2BranchMaterialAddress m hm i)) = _
  rw [branchIncidenceIsometry_apply_address, physicalLegCorrection_apply,
    realPlaneHilbertRotation_neg_comp]

end
end GeometryOfNumbers.Analysis
