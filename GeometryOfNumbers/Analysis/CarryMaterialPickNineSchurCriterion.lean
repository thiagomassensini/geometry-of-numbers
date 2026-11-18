import GeometryOfNumbers.Analysis.CarryMaterialPickNineParity
import Mathlib.Tactic

/-! General Hermitian 8+1 Schur/Sylvester criterion for the physical
fourth Cauchy--Pick direction. No sign is assumed for the full block. -/
open scoped ComplexOrder Matrix MatrixOrder ComplexConjugate
namespace GeometryOfNumbers.Analysis
noncomputable section
set_option autoImplicit false

theorem hermitian_eight_plus_one_posDef_of_corner_posDef_det_pos
    (A : Matrix (Fin 8) (Fin 8) ℂ)
    (B : Matrix (Fin 8) (Fin 1) ℂ)
    (d : ℝ)
    (hA : A.PosDef)
    (hdet : 0 <
      (Matrix.fromBlocks A B Bᴴ (Matrix.diagonal (fun _ : Fin 1 => (d : ℂ)))).det) :
    (Matrix.fromBlocks A B Bᴴ
      (Matrix.diagonal (fun _ : Fin 1 => (d : ℂ)))).PosDef := by
  let D : Matrix (Fin 1) (Fin 1) ℂ :=
    Matrix.diagonal (fun _ : Fin 1 => (d : ℂ))
  letI : Invertible A := hA.isUnit.invertible
  let S : Matrix (Fin 1) (Fin 1) ℂ :=
    D - Bᴴ * A⁻¹ * B
  have hApos : (0 : ℂ) < A.det := hA.det_pos
  have hfactor :
      (Matrix.fromBlocks A B Bᴴ D).det = A.det * S.det := by
    simpa [S] using Matrix.det_fromBlocks₁₁ A B Bᴴ D
  have hSdet : (0 : ℂ) < S.det := by
    rw [hfactor] at hdet
    exact (pos_of_mul_pos_left (by simpa only [mul_comm] using hdet)
      (le_of_lt hApos))
  have hSeq : S = Matrix.diagonal (fun _ : Fin 1 => S.det) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hS : S.PosSemidef := by
    rw [hSeq, Matrix.posSemidef_diagonal_iff]
    exact fun _ => le_of_lt hSdet
  have hM : (Matrix.fromBlocks A B Bᴴ D).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ B D hA).mpr hS
  exact hM.posDef_iff_det_ne_zero.mpr (ne_of_gt hdet)


theorem hermitian_sum_eight_one_posDef_of_corner_posDef_det_pos
    (M : Matrix (Fin 8 ⊕ Fin 1) (Fin 8 ⊕ Fin 1) ℂ)
    (hHerm : M.IsHermitian)
    (hLeading : M.toBlocks₁₁.PosDef)
    (hdet : 0 < M.det) : M.PosDef := by
  let A := M.toBlocks₁₁
  let B := M.toBlocks₁₂
  let C := M.toBlocks₂₁
  let T := M.toBlocks₂₂
  have hC : C = Bᴴ := by
    ext i j
    simpa [C,B,Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
      Matrix.conjTranspose_apply] using
      (hHerm.apply (Sum.inr i) (Sum.inl j)).symm
  have hReal : ((T 0 0).re : ℂ) = T 0 0 := by
    apply Complex.conj_eq_iff_re.mp
    simpa [T, Matrix.toBlocks₂₂] using
      (hHerm.apply (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)))
  have hT : T = Matrix.diagonal (fun _ : Fin 1 => ((T 0 0).re : ℂ)) := by
    ext i j
    fin_cases i
    fin_cases j
    simpa using hReal.symm
  have hM :
      M = Matrix.fromBlocks A B Bᴴ
        (Matrix.diagonal (fun _ : Fin 1 => ((T 0 0).re : ℂ))) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [show M.toBlocks₁₁=A from rfl,
        show M.toBlocks₁₂=B from rfl, ←hC, ←hT]
  rw [hM] at hdet ⊢
  exact hermitian_eight_plus_one_posDef_of_corner_posDef_det_pos A B
    (T 0 0).re hLeading hdet

/-- Finite 3×3 version, preserving the original row order 0,1,2.
The leading 2×2 is the actual restriction to indices 0 and 1. -/
theorem hermitian_fin_nine_posDef_of_leading_posDef_det_pos
    (M : Matrix (Fin 9) (Fin 9) ℂ)
    (hHerm : M.IsHermitian)
    (hLeading : (M.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hdet : 0 < M.det) : M.PosDef := by
  let e : (Fin 8 ⊕ Fin 1) ≃ Fin 9 := finSumFinEquiv
  let R := M.submatrix e e
  have hA : R.toBlocks₁₁.PosDef := by
    convert hLeading using 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hRdet : 0 < R.det := by
    simpa [R, Matrix.det_submatrix_equiv_self] using hdet
  have hR : R.PosDef :=
    hermitian_sum_eight_one_posDef_of_corner_posDef_det_pos R
      (hHerm.submatrix e) hA hRdet
  have hOrig := hR.submatrix (e := e.symm) e.symm.injective
  convert hOrig using 1
  ext i j
  simp [R, e]


#print axioms hermitian_fin_nine_posDef_of_leading_posDef_det_pos

end
end GeometryOfNumbers.Analysis
