import VariationalTransport

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryVariationalSchur
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- An exact invertible coordinate change for the OLD block and its residual.
This changes neither the source nor its physical quadratic form. -/
def scaledOldMatrix {n : ℕ} (d : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal d * A * Matrix.diagonal d

theorem diagonal_isUnit {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    IsUnit (Matrix.diagonal d) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))

theorem scaled_old_isUnit {n : ℕ} (d : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hd : ∀ i, d i ≠ 0) (hA : IsUnit A) : IsUnit (scaledOldMatrix d A) := by
  exact ((diagonal_isUnit d hd).mul hA).mul (diagonal_isUnit d hd)

/-- Inverse residual energy is invariant under the exact diagonal congruence. -/
theorem scaled_inverse_residual {n : ℕ} (d : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) (hA : IsUnit A) :
    r ⬝ᵥ (A⁻¹ *ᵥ r) =
      (Matrix.diagonal d *ᵥ r) ⬝ᵥ ((scaledOldMatrix d A)⁻¹ *ᵥ (Matrix.diagonal d *ᵥ r)) := by
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
  rw [← he]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mulVec_diagonal,u]
  dsimp [w]
  field_simp [hd i]

end
end CarryDirectAnchor
