import GeometryOfNumbers.Analysis.BaseTwoBoundedCenterCoupling

/-! The bounded physical self-coupling inherits the geometric first-cell defect.
No adjoint or block extension is constructed here. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

private def zeroSeedPhysicalInputLinear : PhysicalEdgeL2 →ₗ[ℂ] BaseTwoSeededMaterialHilbert where
  toFun x := WithLp.toLp 2 (0,baseTwoPhysicalEdgeEmbedding x)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp
  map_smul' a x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp

private theorem zeroSeedPhysicalInput_norm (x : PhysicalEdgeL2) :
    ‖zeroSeedPhysicalInputLinear x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [zeroSeedPhysicalInputLinear]

private def zeroSeedPhysicalInput : PhysicalEdgeL2 →L[ℂ] BaseTwoSeededMaterialHilbert :=
  zeroSeedPhysicalInputLinear.mkContinuous 1 (fun x => by
    rw [zeroSeedPhysicalInput_norm]; simp)

/-- Physical-only restriction of the already bounded geometric coupling. -/
def baseTwoPhysicalCenterSelfCoupling : PhysicalEdgeL2 →L[ℂ] PhysicalEdgeL2 :=
  baseTwoCenterCouplingOperator.comp zeroSeedPhysicalInput

@[simp] theorem baseTwoPhysicalCenterSelfCoupling_apply (x : PhysicalEdgeL2)
    (e : BaseTwoPhysicalEdge) :
    baseTwoPhysicalCenterSelfCoupling x e = baseTwoPhysicalCenterSelfCouplingRaw x e := by
  change baseTwoCenterCouplingRaw (WithLp.toLp 2 (0,baseTwoPhysicalEdgeEmbedding x)) e =
    baseTwoCenterCouplingRaw (WithLp.toLp 2 (0,
      baseTwoPhysicalEdgeProjection (baseTwoPhysicalEdgeEmbedding x))) e
  rw [baseTwoPhysicalEdgeProjection_embedding]

/-- Same first-cell matrix as the finite published calculation. -/
theorem baseTwoPhysicalCenterSelfCoupling_first_cell (x : PhysicalEdgeL2) (a : Fin 2) :
    baseTwoPhysicalCenterSelfCoupling x (0,a) =
      (finiteOneCellCenterLogGap a : ℂ) * x (0,0) := by
  rw [baseTwoPhysicalCenterSelfCoupling_apply, baseTwoPhysicalCenterSelfCouplingRaw_first_cell]

theorem baseTwoPhysicalCenterSelfCoupling_inner_left_right :
    inner ℂ (baseTwoPhysicalCenterSelfCoupling baseTwoPhysicalCenterDeltaLeft)
      baseTwoPhysicalCenterDeltaRight = (Real.log 5 - Real.log 4 : ℝ) := by
  change inner ℂ _ (lp.single 2 (0,1) 1) = _
  rw [lp.inner_single_right, baseTwoPhysicalCenterSelfCoupling_apply,
    baseTwoPhysicalCenterSelfCouplingRaw_deltaLeft_first_cell]
  have hg : finiteOneCellCenterLogGap (1 : Fin 2) = Real.log 5 - Real.log 4 := by
    simp [finiteOneCellCenterLogGap, baseTwo_center_eq]
  rw [hg]
  simpa only [RCLike.inner_apply, one_mul] using Complex.conj_ofReal (Real.log 5 - Real.log 4)

theorem baseTwoPhysicalCenterSelfCoupling_inner_right_image :
    inner ℂ baseTwoPhysicalCenterDeltaLeft
      (baseTwoPhysicalCenterSelfCoupling baseTwoPhysicalCenterDeltaRight) = 0 := by
  change inner ℂ (lp.single 2 (0,0) 1) _ = _
  rw [lp.inner_single_left, baseTwoPhysicalCenterSelfCoupling_apply,
    baseTwoPhysicalCenterSelfCouplingRaw_deltaRight_first_cell, inner_zero_right]

/-- Localized failure of symmetry in the unchanged standard physical l2 metric. -/
theorem baseTwoPhysicalCenterSelfCoupling_not_symmetric :
    ¬ baseTwoPhysicalCenterSelfCoupling.toLinearMap.IsSymmetric := by
  intro h
  have he := h baseTwoPhysicalCenterDeltaLeft baseTwoPhysicalCenterDeltaRight
  change inner ℂ (baseTwoPhysicalCenterSelfCoupling baseTwoPhysicalCenterDeltaLeft)
    baseTwoPhysicalCenterDeltaRight = inner ℂ baseTwoPhysicalCenterDeltaLeft
    (baseTwoPhysicalCenterSelfCoupling baseTwoPhysicalCenterDeltaRight) at he
  rw [baseTwoPhysicalCenterSelfCoupling_inner_left_right,
    baseTwoPhysicalCenterSelfCoupling_inner_right_image] at he
  have hp : 0 < Real.log 5 - Real.log 4 :=
    sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))
  exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hp)) he

end GeometryOfNumbers.Analysis.BaseTwoCompletion
