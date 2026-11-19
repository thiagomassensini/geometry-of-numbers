import GeometryOfNumbers.Analysis.CarryMaterialPickThreeSchurCriterion
import Mathlib.Tactic

/-! Fourth-order polarized confluence: exact parity-split determinant.
    This elementary computation does not assume any analytic sign. -/
namespace GeometryOfNumbers.Analysis

/-- At four jet orders the polarized Cauchy-Pick moment array has
even sector [a,b;b,c] and odd sector [b,c;c,d]. -/
theorem c2_four_parity_determinant (a b c d : ℂ) :
    (!![a, 0, b, 0;
        0, b, 0, c;
        b, 0, c, 0;
        0, c, 0, d] : Matrix (Fin 4) (Fin 4) ℂ).det =
      (a*c - b^2)*(b*d-c^2) := by
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix_apply, Fin.succAbove]
  ring

#print axioms c2_four_parity_determinant
end GeometryOfNumbers.Analysis
