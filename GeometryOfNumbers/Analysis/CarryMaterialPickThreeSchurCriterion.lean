import GeometryOfNumbers.Analysis.CarryMaterialComplexPickSignGate
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
Algebraic Schur--Sylvester bridge for a 2+1 Hermitian matrix.
The positive top 2x2 corner and positive full determinant imply the
whole 3x3 matrix is positive definite. This is independent of C2.
-/

open scoped ComplexOrder Matrix MatrixOrder ComplexConjugate

namespace GeometryOfNumbers.Analysis
noncomputable section
set_option autoImplicit false

theorem hermitian_two_plus_one_posDef_of_corner_posDef_det_pos
    (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 1) ℂ)
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

#print axioms hermitian_two_plus_one_posDef_of_corner_posDef_det_pos



/-- A Hermitian block 2+1 matrix with a strictly positive 2×2 corner and
positive full determinant is strictly positive throughout. In contrast
to the previous special lemma, the bottom diagonal is extracted from
the input Hermitian matrix rather than assumed in advance. -/
theorem hermitian_sum_two_one_posDef_of_corner_posDef_det_pos
    (M : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ)
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
  exact hermitian_two_plus_one_posDef_of_corner_posDef_det_pos A B
    (T 0 0).re hLeading hdet

/-- Finite 3×3 version, preserving the original row order 0,1,2.
The leading 2×2 is the actual restriction to indices 0 and 1. -/
theorem hermitian_fin_three_posDef_of_leading_posDef_det_pos
    (M : Matrix (Fin 3) (Fin 3) ℂ)
    (hHerm : M.IsHermitian)
    (hLeading : (M.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hdet : 0 < M.det) : M.PosDef := by
  let e : (Fin 2 ⊕ Fin 1) ≃ Fin 3 := finSumFinEquiv
  let R := M.submatrix e e
  have hA : R.toBlocks₁₁.PosDef := by
    convert hLeading using 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hRdet : 0 < R.det := by
    simpa [R, Matrix.det_submatrix_equiv_self] using hdet
  have hR : R.PosDef :=
    hermitian_sum_two_one_posDef_of_corner_posDef_det_pos R
      (hHerm.submatrix e) hA hRdet
  have hOrig := hR.submatrix (e := e.symm) e.symm.injective
  convert hOrig using 1
  ext i j
  simp [R, e]

#print axioms hermitian_fin_three_posDef_of_leading_posDef_det_pos



/-- Exact Hermitian symmetry of the physical source Pick matrix on EVERY
regular upper-half-plane sample, independent of any sign condition.
This follows from the complex C2 source response, not from PSD. -/
theorem carryMaterialComplexSourcePickMatrix_isHermitian
    (N : ℕ) (z : Fin N → ℂ)
    (hUpper : ∀ i, 0 < (z i).im)
    (hF : ∀ i, carryMaterialComplexValueReadout (z i) ≠ 0) :
    (carryMaterialComplexSourcePickMatrix N z).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  change conj (carryMaterialComplexPickKernel (z j) (z i)) =
    carryMaterialComplexPickKernel (z i) (z j)
  rw [carryMaterialComplexPickKernel_eq_polarizedResponse
      (z j) (z i) (hF j) (hF i)
      (carryMaterialComplexPick_separated_of_positive_im
        (z j) (z i) (hUpper j) (hUpper i)),
    carryMaterialComplexPickKernel_eq_polarizedResponse
      (z i) (z j) (hF i) (hF j)
      (carryMaterialComplexPick_separated_of_positive_im
        (z i) (z j) (hUpper i) (hUpper j))]
  simp only [map_div₀, map_sub, Complex.conj_conj]
  rw [show conj (carryMaterialComplexResponse (z i)) -
      carryMaterialComplexResponse (z j) =
        -(carryMaterialComplexResponse (z j) -
          conj (carryMaterialComplexResponse (z i))) by ring,
      show conj (z i) - z j = -(z j - conj (z i)) by ring]
  exact neg_div_neg_eq _ _



/-- The physical HB diagonal gauge preserves **strict** positivity too.
Nonvanishing of every amplitude supplies invertibility, so the projected
C2 Pick and full source multiplier defect have identical strict inertia. -/
theorem carryMaterialComplexSourcePickMatrix_posDef_iff_sourceDefect
    (N : ℕ) (z : Fin N → ℂ)
    (hUpper : ∀ i, 0 < (z i).im)
    (hF : ∀ i, carryMaterialComplexValueReadout (z i) ≠ 0)
    (hHB : ∀ i, carryMaterialComplexPositiveHB (z i) ≠ 0) :
    (carryMaterialComplexSourcePickMatrix N z).PosDef ↔
      (carryMaterialComplexSourceDefectMatrix N z).PosDef := by
  have hUnit : IsUnit (carryMaterialComplexSourceGaugeMatrix N z) := by
    rw [carryMaterialComplexSourceGaugeMatrix,
      Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro i
    apply isUnit_iff_ne_zero.mpr
    unfold carryMaterialComplexChiralGauge
    exact div_ne_zero (hHB i) (mul_ne_zero (by norm_num) (hF i))
  rw [carryMaterialComplexSourcePickMatrix_eq_gaugedDefect N z hUpper hF hHB]
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.IsUnit.posDef_star_left_conjugate_iff
      (U := carryMaterialComplexSourceGaugeMatrix N z)
      (x := carryMaterialComplexSourceDefectMatrix N z) hUnit)

#print axioms carryMaterialComplexSourcePickMatrix_posDef_iff_sourceDefect

end
end GeometryOfNumbers.Analysis
