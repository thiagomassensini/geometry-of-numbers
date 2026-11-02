import TenExplicitCutoff

namespace CarryExplicitBudget
open CarrySelfAdjointOperator CarryDirectAnchor CarryIntegralCertificate CarryVariationalSchur
open CarryCriticalRadialMargin CarryCriticalSource CarrySummableRadial
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option maxRecDepth 65536
attribute [local irreducible] Box.Mem

/-- Exact congruence transport of a solve: this changes coordinates only. -/
theorem scaled_inverse_apply {n : ℕ} (d : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (hA : IsUnit A) :
    A⁻¹ *ᵥ r = Matrix.diagonal d *ᵥ ((scaledOldMatrix d A)⁻¹ *ᵥ (Matrix.diagonal d *ᵥ r)) := by
  let w := A⁻¹ *ᵥ r
  let u : Fin n → ℝ := fun i => w i / d i
  letI := hA.invertible
  have hw : A *ᵥ w = r := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]
  have hdu : Matrix.diagonal d *ᵥ u = w := by
    ext i
    simp only [Matrix.mulVec_diagonal,u]
    field_simp [hd i]
  have hbu : scaledOldMatrix d A *ᵥ u = Matrix.diagonal d *ᵥ r := by
    unfold scaledOldMatrix
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,hdu,hw]
  letI := (scaled_old_isUnit d A hd hA).invertible
  have he := congrArg (fun v => (scaledOldMatrix d A)⁻¹ *ᵥ v) hbu
  rw [Matrix.mulVec_mulVec,Matrix.inv_mul_of_invertible,Matrix.one_mulVec] at he
  change w = _
  rw [← he,hdu]

def correctionNumeratorBox (i : Fin 4) : Box := Box.sum
  (fun j => (adjBoxAt i.val j).mul (residualBoxAt j)) 4

def correctionAt (i : Fin 4) : ℝ := (oldMatrix⁻¹ *ᵥ oldResidual) i

def correctionBox (i : Fin 4) : Box :=
  (Box.point (scaleInt i)).mul ((correctionNumeratorBox i).div scaledDetBox)

theorem correction_numerator_box_mem (i : Fin 4) :
    (correctionNumeratorBox i).Mem (∑ j : Fin 4, scaledMatrix.adjugate i j * scaledResidual j) := by
  have h := mem_sum (fun j => (adjBoxAt i.val j).mul (residualBoxAt j))
    (fun j => adjAt i.val j * residualAt j) 4 (by
      intro j hj
      have hi : i.val < 4 := i.isLt
      simp only [adjBoxAt,residualBoxAt,adjAt,residualAt,dif_pos hi,dif_pos hj]
      exact mem_mul (adj_box_mem i ⟨j,hj⟩) (residual_box_mem ⟨j,hj⟩))
  convert h using 1
  · rfl
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hi : i.val < 4 := i.isLt
    simp [adjAt,residualAt,hi,j.isLt]

theorem correction_box_mem (i : Fin 4) : (correctionBox i).Mem (correctionAt i) := by
  have h := mem_mul (mem_point (scaleInt i))
    (mem_div (correction_numerator_box_mem i) scaled_det_box_mem)
  convert h using 1
  · rfl
  · unfold correctionAt
    rw [scaled_inverse_apply scaleReal oldMatrix oldResidual scale_ne_zero ten_old_block_isUnit]
    simp only [Matrix.mulVec_diagonal]
    change scaleReal i * ((scaledMatrix⁻¹ *ᵥ scaledResidual) i) = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec]
    simp only [Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,scaleReal,div_eq_mul_inv]
    ring

theorem correction_bounded (i : Fin 4) : |correctionAt i| ≤ 1 := by
  have h := mem_of_contained (correction_box_mem i)
    (show (correctionBox i).contained (.finite (-intervalScale) intervalScale)=true by
      fin_cases i <;> decide +kernel)
  norm_num [Box.Mem,intervalScale] at h
  apply abs_le.mpr
  constructor <;> nlinarith [h.1,h.2]

end
end CarryExplicitBudget
