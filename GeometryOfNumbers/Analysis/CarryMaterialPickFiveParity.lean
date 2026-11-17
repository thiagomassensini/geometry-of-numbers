import GeometryOfNumbers.Analysis.CarryMaterialPickFourParity
import Mathlib.Tactic

/-! Exact fifth parity split for the completed Cauchy--Pick confluent
coefficient array, with NO positivity hypothesis. -/
namespace GeometryOfNumbers.Analysis
open scoped Matrix

noncomputable def fiveParityReindex : (Fin 3 ⊕ Fin 2) ≃ Fin 5 :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl i => (⟨2*i.val, by omega⟩ : Fin 5)
      | Sum.inr j => (⟨2*j.val+1, by omega⟩ : Fin 5))
    (by decide)

theorem c2_five_parity_determinant (a b c d e : ℂ) :
    (!![a, 0, b, 0, c;
        0, b, 0, c, 0;
        b, 0, c, 0, d;
        0, c, 0, d, 0;
        c, 0, d, 0, e] : Matrix (Fin 5) (Fin 5) ℂ).det =
      (!![a,b,c;b,c,d;c,d,e] : Matrix (Fin 3) (Fin 3) ℂ).det *
      (!![b,c;c,d] : Matrix (Fin 2) (Fin 2) ℂ).det := by
  let M : Matrix (Fin 5) (Fin 5) ℂ :=
    !![a, 0, b, 0, c;
       0, b, 0, c, 0;
       b, 0, c, 0, d;
       0, c, 0, d, 0;
       c, 0, d, 0, e]
  let E : Matrix (Fin 3) (Fin 3) ℂ := !![a,b,c;b,c,d;c,d,e]
  let O : Matrix (Fin 2) (Fin 2) ℂ := !![b,c;c,d]
  let f := fiveParityReindex
  have hR : M.submatrix f f =
      Matrix.fromBlocks E 0 0 O := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [M,E,O,f,fiveParityReindex, Matrix.fromBlocks]
  change M.det = E.det * O.det
  calc
    M.det = (M.submatrix f f).det := (Matrix.det_submatrix_equiv_self f M).symm
    _ = (Matrix.fromBlocks E 0 0 O).det := by rw [hR]
    _ = E.det * O.det := Matrix.det_fromBlocks_zero₂₁ E 0 O

#print axioms c2_five_parity_determinant
end GeometryOfNumbers.Analysis
