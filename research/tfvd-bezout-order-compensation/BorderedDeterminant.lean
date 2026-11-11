import RankOneUpdate

namespace CarrySourceBezout
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- Adding one scalar only at the last diagonal changes a determinant by that
scalar times the determinant of the leading principal submatrix. This formula
does not assume the leading block is invertible. -/
theorem det_add_lastCoordinateMatrix {n : ℕ} (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (a : ℝ) :
    (M + lastCoordinateMatrix n a).det =
      M.det + a * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last n), Matrix.det_succ_row _ (Fin.last n)]
  simp only [Fin.sum_univ_castSucc]
  have hentry (i : Fin n) :
      (M + lastCoordinateMatrix n a) (Fin.last n) i.castSucc =
        M (Fin.last n) i.castSucc := by
    have hi : i.val ≠ n := by omega
    simp [Matrix.add_apply, lastCoordinateMatrix, hi]
  have hminor (i : Fin n) :
      ((M + lastCoordinateMatrix n a).submatrix (Fin.last n).succAbove
        i.castSucc.succAbove).det =
        (M.submatrix (Fin.last n).succAbove i.castSucc.succAbove).det := by
    congr 1
    ext j k
    have hj : j.val ≠ n := by omega
    simp [Matrix.submatrix, Fin.succAbove_last, Matrix.add_apply,
      lastCoordinateMatrix, hj]
  have hrest :
      (∑ i : Fin n, (-1 : ℝ) ^ ((Fin.last n).val + i.castSucc.val) *
        (M + lastCoordinateMatrix n a) (Fin.last n) i.castSucc *
          ((M + lastCoordinateMatrix n a).submatrix (Fin.last n).succAbove
            i.castSucc.succAbove).det) =
      ∑ i : Fin n, (-1 : ℝ) ^ ((Fin.last n).val + i.castSucc.val) *
        M (Fin.last n) i.castSucc *
          (M.submatrix (Fin.last n).succAbove i.castSucc.succAbove).det := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hentry, hminor]
  have hlastMinor :
      ((M + lastCoordinateMatrix n a).submatrix (Fin.last n).succAbove
        (Fin.last n).succAbove).det =
        (M.submatrix Fin.castSucc Fin.castSucc).det := by
    congr 1
    ext i j
    have hi : i.val ≠ n := by omega
    simp [Matrix.submatrix, Fin.succAbove_last, Matrix.add_apply,
      lastCoordinateMatrix, hi]
  have hlastMinorOld :
      (M.submatrix (Fin.last n).succAbove (Fin.last n).succAbove).det =
        (M.submatrix Fin.castSucc Fin.castSucc).det := by
    congr 1
    ext i j
    simp [Matrix.submatrix, Fin.succAbove_last]
  have hlastEntry :
      (M + lastCoordinateMatrix n a) (Fin.last n) (Fin.last n) =
        M (Fin.last n) (Fin.last n) + a := by
    simp [Matrix.add_apply, lastCoordinateMatrix]
  have hsign : (-1 : ℝ) ^ ((Fin.last n).val + (Fin.last n).val) = 1 := by
    rw [Fin.val_last, show n+n = 2*n by omega, pow_mul]
    norm_num
  rw [hrest, hlastEntry, hlastMinor, hlastMinorOld, hsign]
  ring

theorem coefficientBlock_prefix (f : BiSeries ℝ) (n : ℕ) :
    (coefficientBlock f (n+1)).submatrix Fin.castSucc Fin.castSucc =
      coefficientBlock f n := by
  ext i j
  rfl

/-- Determinant version of the rank-one source update. The determinant is
affine in the new coefficient even if its prefix determinant is zero. -/
theorem sourceBezout_borderedDet_lastCoefficient
    (c : ℕ → ℝ) (n : ℕ) (b : Bool) (δ : ℝ) :
    (coefficientBlock
      (sourceKernel (sourceCoefficientUpdate c (if b then 2*n+2 else 2*n+1) δ) b)
      (n+1)).det =
        (coefficientBlock (sourceKernel c b) (n+1)).det -
          ((if b then 2*n+2 else 2*n+1 : ℕ) : ℝ) * c 0 * δ *
            (coefficientBlock (sourceKernel c b) n).det := by
  rw [sourceBezout_lastCoefficient_rankOne]
  rw [det_add_lastCoordinateMatrix, coefficientBlock_prefix]
  ring

#print axioms det_add_lastCoordinateMatrix
#print axioms coefficientBlock_prefix
#print axioms sourceBezout_borderedDet_lastCoefficient

end
end CarrySourceBezout
