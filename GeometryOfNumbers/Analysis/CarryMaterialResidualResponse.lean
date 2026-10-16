import GeometryOfNumbers.Analysis.CarryMaterialNormalizedResponse

/-! The first reduction of the actual material response, with its removable
real divided slopes. No kernel or metric is chosen as input. -/
namespace GeometryOfNumbers.Analysis
open BaseTwoCompletion
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def carryMaterialReducedResponse (t : ℝ) : ℂ :=
  dslope carryMaterialResponseAxis 0 t /
    ((carryMaterialResponseScale : ℂ) * carryMaterialResponseAxis t)

/-- The physical residual coordinate channel of the actual source is already
nonzero at the origin. This is not the weighted Schur residual kernel. -/
theorem carryMaterial_physical_residual_origin_norm_pos :
    0 < ‖baseTwoResidualEdgeProjection (baseTwoCompletedMaterialGradientL2 0)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have h := congrArg (fun g : MaterialEdgeL2 => (g 0).re) hz
  change (if ¬ ((0 : ℕ) % 4 = 2 ∨ 0 % 4 = 3) then
    (baseTwoCompletedMaterialGradientL2 0) 0 else 0).re = 0 at h
  norm_num [baseTwoCompletedMaterialGradientL2_apply, baseTwoCompletedMaterialGradient_apply,
    criticalMaterialGradient, criticalMaterialSample] at h
  have hs := Real.sqrt_nonneg (2 : ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith

end
end GeometryOfNumbers.Analysis
