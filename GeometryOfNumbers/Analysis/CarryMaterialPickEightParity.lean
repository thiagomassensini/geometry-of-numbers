import GeometryOfNumbers.Analysis.CarryMaterialPickSevenParity
import Mathlib.Tactic

/-! Exact parity split of the 8×8 original confluent coefficient matrix:
no positivity assumption or discarded crossings. -/
namespace GeometryOfNumbers.Analysis
open scoped Matrix

noncomputable def eightParityReindex : (Fin 4 ⊕ Fin 4) ≃ Fin 8 :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl i => (⟨2*i.val, by omega⟩ : Fin 8)
      | Sum.inr j => (⟨2*j.val+1, by omega⟩ : Fin 8))
    (by decide)

theorem c2_eight_parity_determinant (a b c d e f g h : ℂ) :
    (!![a, 0, b, 0, c, 0, d, 0;
        0, b, 0, c, 0, d, 0, e;
        b, 0, c, 0, d, 0, e, 0;
        0, c, 0, d, 0, e, 0, f;
        c, 0, d, 0, e, 0, f, 0;
        0, d, 0, e, 0, f, 0, g;
        d, 0, e, 0, f, 0, g, 0;
        0, e, 0, f, 0, g, 0, h] : Matrix (Fin 8) (Fin 8) ℂ).det =
      (!![a,b,c,d;b,c,d,e;c,d,e,f;d,e,f,g] : Matrix (Fin 4) (Fin 4) ℂ).det *
      (!![b,c,d,e;c,d,e,f;d,e,f,g;e,f,g,h] : Matrix (Fin 4) (Fin 4) ℂ).det := by
  let M : Matrix (Fin 8) (Fin 8) ℂ := !![a, 0, b, 0, c, 0, d, 0;
        0, b, 0, c, 0, d, 0, e;
        b, 0, c, 0, d, 0, e, 0;
        0, c, 0, d, 0, e, 0, f;
        c, 0, d, 0, e, 0, f, 0;
        0, d, 0, e, 0, f, 0, g;
        d, 0, e, 0, f, 0, g, 0;
        0, e, 0, f, 0, g, 0, h]
  let E : Matrix (Fin 4) (Fin 4) ℂ := !![a,b,c,d;b,c,d,e;c,d,e,f;d,e,f,g]
  let O : Matrix (Fin 4) (Fin 4) ℂ := !![b,c,d,e;c,d,e,f;d,e,f,g;e,f,g,h]
  let q := eightParityReindex
  have hR : M.submatrix q q = Matrix.fromBlocks E 0 0 O := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [M,E,O,q,eightParityReindex,Matrix.fromBlocks]
  change M.det = E.det * O.det
  calc
    M.det = (M.submatrix q q).det := (Matrix.det_submatrix_equiv_self q M).symm
    _ = (Matrix.fromBlocks E 0 0 O).det := by rw [hR]
    _ = E.det * O.det := Matrix.det_fromBlocks_zero₂₁ E 0 O

#print axioms c2_eight_parity_determinant
end GeometryOfNumbers.Analysis
