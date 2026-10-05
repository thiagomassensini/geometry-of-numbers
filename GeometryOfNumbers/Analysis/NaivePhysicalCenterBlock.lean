import GeometryOfNumbers.Analysis.BaseTwoCenterSectorAdjointMismatch

/-! A localized test of the standard single-center product block.
No doubled center, graph/return realization or dilation is constructed. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators lp ENNReal
namespace GeometryOfNumbers.Analysis.BaseTwoCompletion

abbrev BaseTwoPhysicalCenterHilbert := WithLp 2 (PhysicalEdgeL2 × BaseTwoCenterL2)

private def naivePhysicalCenterBlockLinear : BaseTwoPhysicalCenterHilbert →ₗ[ℂ] BaseTwoPhysicalCenterHilbert where
  toFun y := WithLp.toLp 2 (baseTwoCenterLegSynthesis y.snd,baseTwoPhysicalCenterReconstruction y.fst)
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp
  map_smul' a y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext <;> simp

private theorem naivePhysicalCenterBlock_norm_le (y : BaseTwoPhysicalCenterHilbert) :
    ‖naivePhysicalCenterBlockLinear y‖ ≤ 4*‖y‖ := by
  have ht : ‖baseTwoPhysicalCenterReconstruction y.fst‖ ≤ 4*‖y.fst‖ := by
    change ‖baseTwoNormalizedCenterReconstruction (baseTwoPhysicalToSeeded y.fst)‖ ≤ 4*‖y.fst‖
    have h := baseTwoNormalizedCenterReconstruction_norm_le (baseTwoPhysicalToSeeded y.fst)
    simpa only [baseTwoPhysicalToSeeded_norm] using h
  have hp := pow_le_pow_left₀ (norm_nonneg _) ht 2
  have hb := WithLp.prod_norm_sq_eq_of_L2 (naivePhysicalCenterBlockLinear y)
  change ‖naivePhysicalCenterBlockLinear y‖^2 =
    ‖baseTwoCenterLegSynthesis y.snd‖^2 + ‖baseTwoPhysicalCenterReconstruction y.fst‖^2 at hb
  rw [baseTwoCenterLegSynthesis_norm] at hb
  have hy := WithLp.prod_norm_sq_eq_of_L2 y
  nlinarith [norm_nonneg y,norm_nonneg (naivePhysicalCenterBlockLinear y),sq_nonneg ‖y.snd‖]

/-- Exactly the naive block (p,c) -> (S c,T_phys p), in the standard product. -/
def naivePhysicalCenterBlock : BaseTwoPhysicalCenterHilbert →L[ℂ] BaseTwoPhysicalCenterHilbert :=
  naivePhysicalCenterBlockLinear.mkContinuous 4 naivePhysicalCenterBlock_norm_le

@[simp] theorem naivePhysicalCenterBlock_apply (y : BaseTwoPhysicalCenterHilbert) :
    naivePhysicalCenterBlock y =
      WithLp.toLp 2 (baseTwoCenterLegSynthesis y.snd,baseTwoPhysicalCenterReconstruction y.fst) := rfl

/-- Symmetry of the product block would force the already refuted adjoint identity. -/
theorem naivePhysicalCenterBlock_not_symmetric :
    ¬ naivePhysicalCenterBlock.toLinearMap.IsSymmetric := by
  intro h
  apply baseTwoPhysicalCenterReconstruction_ne_legSynthesis_adjoint
  apply ContinuousLinearMap.ext
  intro p
  apply ext_inner_right ℂ
  intro c
  rw [ContinuousLinearMap.adjoint_inner_left]
  have he := h (WithLp.toLp 2 (p,0)) (WithLp.toLp 2 (0,c))
  rw [WithLp.prod_inner_apply,WithLp.prod_inner_apply] at he
  change inner ℂ (baseTwoCenterLegSynthesis 0) 0 +
    inner ℂ (baseTwoPhysicalCenterReconstruction p) c =
    inner ℂ p (baseTwoCenterLegSynthesis c) + inner ℂ 0 (baseTwoPhysicalCenterReconstruction 0) at he
  change inner ℂ (baseTwoPhysicalCenterReconstruction p) c = inner ℂ p (baseTwoCenterLegSynthesis c)
  simpa only [inner_zero_right,inner_zero_left,zero_add,add_zero] using he

end GeometryOfNumbers.Analysis.BaseTwoCompletion
