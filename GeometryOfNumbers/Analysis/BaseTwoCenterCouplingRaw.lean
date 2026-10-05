import GeometryOfNumbers.Analysis.FinitePhysicalCenterCoupling

/-! # Geometric raw center coupling and physical Hilbert zero-extension
Reconstruction uses seed and a finite material-edge prefix. These raw center
coordinates are not asserted to be in l2. Coupling is linear before any Hardy
bound and its concrete orbit recovers the certified center-clock defect.
-/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion
open GreenFrame.Concrete

abbrev BaseTwoSeededMaterialHilbert := WithLp 2 (ℂ × MaterialEdgeL2)
abbrev PhysicalEdgeL2 := ℓ²(BaseTwoPhysicalEdge,ℂ)

/-- All preceding material edges; no infinite nodal state is constructed. -/
def baseTwoCenterReconstruction : BaseTwoSeededMaterialHilbert →ₗ[ℂ] (ℕ → ℂ) where
  toFun y k := y.fst + ∑ j ∈ Finset.range (baseTwoCenter k - 1), y.snd j
  map_add' x y := by funext k; simp [Finset.sum_add_distrib]; ring
  map_smul' a x := by funext k; simp [Finset.mul_sum, mul_add]

def baseTwoCenterLogGap (e : BaseTwoPhysicalEdge) : ℝ :=
  if e.2.val = 0 then Real.log (baseTwoCenter e.1 : ℝ) -
      Real.log ((baseTwoCenter e.1 - 1 : ℕ) : ℝ)
    else Real.log ((baseTwoCenter e.1 + 1 : ℕ) : ℝ) - Real.log (baseTwoCenter e.1 : ℝ)

/-- Defined from reconstruction and cell log gaps, independently of the orbit. -/
def baseTwoCenterCouplingRaw :
    BaseTwoSeededMaterialHilbert →ₗ[ℂ] (BaseTwoPhysicalEdge → ℂ) where
  toFun y e := (baseTwoCenterLogGap e : ℂ) * baseTwoCenterReconstruction y e.1
  map_add' x y := by funext e; simp [map_add, mul_add]
  map_smul' a x := by funext e; simp [map_smul]; ring

def baseTwoConcreteSeededGradientState (t : ℝ) : BaseTwoSeededMaterialHilbert :=
  WithLp.toLp 2 (criticalMaterialSample t 1, baseTwoCompletedMaterialGradientL2 t)

theorem baseTwoCenterReconstruction_concrete (t : ℝ) (k : ℕ) :
    baseTwoCenterReconstruction (baseTwoConcreteSeededGradientState t) k =
      criticalMaterialSample t (baseTwoCenter k) := by
  have h := criticalMaterialSample_eq_seed_add_gradientPrefix t (baseTwoCenter k - 1)
  have hc : baseTwoCenter k - 1 + 1 = baseTwoCenter k := by simp [baseTwo_center_eq]; omega
  rw [hc] at h
  exact h.symm

/-- The orbit defect is a consequence of geometric reconstruction. -/
theorem baseTwoCenterCouplingRaw_concrete (t : ℝ) :
    baseTwoCenterCouplingRaw (baseTwoConcreteSeededGradientState t) =
      baseTwoPhysicalCenterClockDefect t := by
  funext e
  change (baseTwoCenterLogGap e : ℂ) *
    baseTwoCenterReconstruction (baseTwoConcreteSeededGradientState t) e.1 = _
  rw [baseTwoCenterReconstruction_concrete]
  rcases e with ⟨k,a⟩
  fin_cases a
  · change ((Real.log (baseTwoCenter k : ℝ) -
      Real.log ((baseTwoCenter k - 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      criticalMaterialSample t (baseTwoCenter k) = baseTwoPhysicalCenterClockDefect t (k,0)
    rw [baseTwoPhysicalCenterClockDefect_left, Complex.ofReal_sub]
  · change ((Real.log ((baseTwoCenter k + 1 : ℕ) : ℝ) -
      Real.log (baseTwoCenter k : ℝ) : ℝ) : ℂ) *
      criticalMaterialSample t (baseTwoCenter k) = baseTwoPhysicalCenterClockDefect t (k,1)
    rw [baseTwoPhysicalCenterClockDefect_right, Complex.ofReal_sub]

def baseTwoCenterCouplingSeedRaw (z : ℂ) : BaseTwoPhysicalEdge → ℂ :=
  baseTwoCenterCouplingRaw (WithLp.toLp 2 (z,0))

def baseTwoCenterCouplingPhysicalRaw (g : MaterialEdgeL2) : BaseTwoPhysicalEdge → ℂ :=
  baseTwoCenterCouplingRaw (WithLp.toLp 2 (0,baseTwoPhysicalEdgeProjection g))

def baseTwoCenterCouplingResidualRaw (g : MaterialEdgeL2) : BaseTwoPhysicalEdge → ℂ :=
  baseTwoCenterCouplingRaw (WithLp.toLp 2 (0,baseTwoResidualEdgeProjection g))

/-- All three pieces are retained; residual alone is not the center source. -/
theorem baseTwoCenterCouplingRaw_seed_physical_residual (y : BaseTwoSeededMaterialHilbert) :
    baseTwoCenterCouplingRaw y = baseTwoCenterCouplingSeedRaw y.fst +
      baseTwoCenterCouplingPhysicalRaw y.snd + baseTwoCenterCouplingResidualRaw y.snd := by
  have he : y = WithLp.toLp 2 (y.fst,0) +
      WithLp.toLp 2 (0,baseTwoPhysicalEdgeProjection y.snd) +
      WithLp.toLp 2 (0,baseTwoResidualEdgeProjection y.snd) := by
    apply WithLp.ofLp_injective 2; apply Prod.ext
    · simp
    · simpa using (baseTwoPhysicalResidual_reconstruction y.snd).symm
  conv_lhs => rw [he, map_add, map_add]
  rfl

private def physicalEdgeExtension (x : PhysicalEdgeL2) : MaterialEdgeL2 :=
  ⟨Function.extend baseTwoPhysicalEdgeIndex x 0, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have he : (fun n => ‖Function.extend baseTwoPhysicalEdgeIndex x 0 n‖^2) =
        Function.extend baseTwoPhysicalEdgeIndex (fun e => ‖x e‖^2) 0 := by
      funext n
      by_cases hn : ∃ e, baseTwoPhysicalEdgeIndex e = n
      · obtain ⟨e,rfl⟩ := hn
        rw [baseTwoPhysicalEdgeIndex_injective.extend_apply,
          baseTwoPhysicalEdgeIndex_injective.extend_apply]
      · rw [Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
        simp
    rw [he]
    exact (summable_extend_zero baseTwoPhysicalEdgeIndex_injective).mpr
      (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))⟩

private def physicalEdgeExtensionLinear : PhysicalEdgeL2 →ₗ[ℂ] MaterialEdgeL2 where
  toFun := physicalEdgeExtension
  map_add' x y := by
    apply lp.ext; funext n
    by_cases hn : ∃ e, baseTwoPhysicalEdgeIndex e = n
    · obtain ⟨e,rfl⟩ := hn
      simp [physicalEdgeExtension, baseTwoPhysicalEdgeIndex_injective.extend_apply]
    · simp [physicalEdgeExtension, Function.extend_apply' _ _ _ hn]
  map_smul' a x := by
    apply lp.ext; funext n
    by_cases hn : ∃ e, baseTwoPhysicalEdgeIndex e = n
    · obtain ⟨e,rfl⟩ := hn
      simp [physicalEdgeExtension, baseTwoPhysicalEdgeIndex_injective.extend_apply]
    · simp [physicalEdgeExtension, Function.extend_apply' _ _ _ hn]

private theorem physicalEdgeExtension_norm (x : PhysicalEdgeL2) :
    ‖physicalEdgeExtension x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hx := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x
  have hy := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (physicalEdgeExtension x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx hy
  rw [hy, hx]
  have he : (fun n => ‖physicalEdgeExtension x n‖^2) =
      Function.extend baseTwoPhysicalEdgeIndex (fun e => ‖x e‖^2) 0 := by
    funext n
    by_cases hn : ∃ e, baseTwoPhysicalEdgeIndex e = n
    · obtain ⟨e,rfl⟩ := hn
      simp [physicalEdgeExtension, baseTwoPhysicalEdgeIndex_injective.extend_apply]
    · simp [physicalEdgeExtension, Function.extend_apply' _ _ _ hn]
  rw [he, tsum_extend_zero baseTwoPhysicalEdgeIndex_injective]

/-- Canonical complex-linear zero-extension, with the unchanged l2 norm. -/
def baseTwoPhysicalEdgeEmbedding : PhysicalEdgeL2 →ₗᵢ[ℂ] MaterialEdgeL2 :=
  { physicalEdgeExtensionLinear with norm_map' := physicalEdgeExtension_norm }

theorem baseTwoPhysicalEdgeEmbedding_apply (x : PhysicalEdgeL2) (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalEdgeEmbedding x (baseTwoPhysicalEdgeIndex e) = x e :=
  baseTwoPhysicalEdgeIndex_injective.extend_apply _ _ e

theorem baseTwoPhysicalEdgeEmbedding_off_sector (x : PhysicalEdgeL2) (n : ℕ)
    (hn : n ∉ Set.range baseTwoPhysicalEdgeIndex) : baseTwoPhysicalEdgeEmbedding x n = 0 :=
  Function.extend_apply' _ _ _ hn

theorem baseTwoPhysicalEdgeRestriction_embedding (x : PhysicalEdgeL2) :
    baseTwoPhysicalEdgeRestriction (baseTwoPhysicalEdgeEmbedding x) = x := by
  apply lp.ext; funext e
  rw [baseTwoPhysicalEdgeRestriction_apply, baseTwoPhysicalEdgeEmbedding_apply]

theorem baseTwoPhysicalEdgeEmbedding_restriction (g : MaterialEdgeL2) :
    baseTwoPhysicalEdgeEmbedding (baseTwoPhysicalEdgeRestriction g) =
      baseTwoPhysicalEdgeProjection g := by
  apply lp.ext; funext n
  change baseTwoPhysicalEdgeEmbedding (baseTwoPhysicalEdgeRestriction g) n =
    if n % 4 = 2 ∨ n % 4 = 3 then g n else 0
  by_cases hn : n ∈ Set.range baseTwoPhysicalEdgeIndex
  · obtain ⟨e,rfl⟩ := hn
    rw [baseTwoPhysicalEdgeEmbedding_apply, baseTwoPhysicalEdgeRestriction_apply,
      if_pos ((baseTwoPhysicalEdgeIndex_range _).mp ⟨e,rfl⟩)]
  · rw [baseTwoPhysicalEdgeEmbedding_off_sector _ _ hn,
      if_neg (fun h => hn ((baseTwoPhysicalEdgeIndex_range _).mpr h))]

theorem baseTwoPhysicalEdgeProjection_embedding (x : PhysicalEdgeL2) :
    baseTwoPhysicalEdgeProjection (baseTwoPhysicalEdgeEmbedding x) = baseTwoPhysicalEdgeEmbedding x := by
  rw [← baseTwoPhysicalEdgeEmbedding_restriction, baseTwoPhysicalEdgeRestriction_embedding]

/-- Raw physical self-coupling; membership/boundedness is not assumed. -/
def baseTwoPhysicalCenterSelfCouplingRaw (x : PhysicalEdgeL2) : BaseTwoPhysicalEdge → ℂ :=
  baseTwoCenterCouplingPhysicalRaw (baseTwoPhysicalEdgeEmbedding x)

/-- The first-cell compression is literally the previously published finite block. -/
theorem baseTwoPhysicalCenterSelfCouplingRaw_first_cell (x : PhysicalEdgeL2) (a : Fin 2) :
    baseTwoPhysicalCenterSelfCouplingRaw x (0,a) =
      (finiteOneCellCenterLogGap a : ℂ) * x (0,0) := by
  unfold baseTwoPhysicalCenterSelfCouplingRaw baseTwoCenterCouplingPhysicalRaw
  rw [baseTwoPhysicalEdgeProjection_embedding]
  change (baseTwoCenterLogGap (0,a) : ℂ) *
    ((0 : ℂ) + ∑ j ∈ Finset.range (baseTwoCenter 0 - 1), baseTwoPhysicalEdgeEmbedding x j) = _
  have h0 : (0 : ℕ) ∉ Set.range baseTwoPhysicalEdgeIndex := by
    rw [baseTwoPhysicalEdgeIndex_range]; norm_num
  have h1 : (1 : ℕ) ∉ Set.range baseTwoPhysicalEdgeIndex := by
    rw [baseTwoPhysicalEdgeIndex_range]; norm_num
  have h2 : baseTwoPhysicalEdgeEmbedding x 2 = x (0,0) := by
    simpa only [baseTwoPhysicalEdgeIndex_left, Nat.mul_zero, Nat.zero_add] using
      baseTwoPhysicalEdgeEmbedding_apply x (0,0)
  simp [baseTwo_center_eq, Finset.sum_range_succ,
    baseTwoPhysicalEdgeEmbedding_off_sector x 0 h0,
    baseTwoPhysicalEdgeEmbedding_off_sector x 1 h1, h2]
  left; rfl

/-- Standard physical deltas, defined independently of any coupling or moment. -/
def baseTwoPhysicalCenterDeltaLeft : PhysicalEdgeL2 := lp.single 2 (0,0) 1

def baseTwoPhysicalCenterDeltaRight : PhysicalEdgeL2 := lp.single 2 (0,1) 1

theorem baseTwoPhysicalCenterSelfCouplingRaw_deltaLeft_first_cell (a : Fin 2) :
    baseTwoPhysicalCenterSelfCouplingRaw baseTwoPhysicalCenterDeltaLeft (0,a) =
      (finiteOneCellCenterLogGap a : ℂ) := by
  rw [baseTwoPhysicalCenterSelfCouplingRaw_first_cell]
  simp [baseTwoPhysicalCenterDeltaLeft, lp.single_apply]

theorem baseTwoPhysicalCenterSelfCouplingRaw_deltaRight_first_cell (a : Fin 2) :
    baseTwoPhysicalCenterSelfCouplingRaw baseTwoPhysicalCenterDeltaRight (0,a) = 0 := by
  rw [baseTwoPhysicalCenterSelfCouplingRaw_first_cell]
  simp [baseTwoPhysicalCenterDeltaRight, lp.single_apply]

end GeometryOfNumbers.Analysis.BaseTwoCompletion
