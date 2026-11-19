import GeometryOfNumbers.Analysis.CarryMaterialPickFiveParity
import Mathlib.Tactic

/-!
Exact parity reindexing of the 6×6 confluent Cauchy–Pick coefficient
matrix. No positivity is assumed. Even and odd 3×3 source
blocks use their original Taylor coefficients.
-/
namespace GeometryOfNumbers.Analysis
open scoped Matrix

noncomputable def sixParityReindex : (Fin 3 ⊕ Fin 3) ≃ Fin 6 :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl i => (⟨2*i.val, by omega⟩ : Fin 6)
      | Sum.inr j => (⟨2*j.val+1, by omega⟩ : Fin 6))
    (by decide)

theorem c2_six_parity_determinant (a b c d e f : ℂ) :
    (!![a, 0, b, 0, c, 0;
        0, b, 0, c, 0, d;
        b, 0, c, 0, d, 0;
        0, c, 0, d, 0, e;
        c, 0, d, 0, e, 0;
        0, d, 0, e, 0, f] : Matrix (Fin 6) (Fin 6) ℂ).det =
      (!![a,b,c;b,c,d;c,d,e] : Matrix (Fin 3) (Fin 3) ℂ).det *
      (!![b,c,d;c,d,e;d,e,f] : Matrix (Fin 3) (Fin 3) ℂ).det := by
  let M : Matrix (Fin 6) (Fin 6) ℂ :=
    !![a, 0, b, 0, c, 0;
       0, b, 0, c, 0, d;
       b, 0, c, 0, d, 0;
       0, c, 0, d, 0, e;
       c, 0, d, 0, e, 0;
       0, d, 0, e, 0, f]
  let E : Matrix (Fin 3) (Fin 3) ℂ := !![a,b,c;b,c,d;c,d,e]
  let O : Matrix (Fin 3) (Fin 3) ℂ := !![b,c,d;c,d,e;d,e,f]
  let g := sixParityReindex
  have hR : M.submatrix g g =
      Matrix.fromBlocks E 0 0 O := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [M,E,O,g,sixParityReindex,Matrix.fromBlocks]
  change M.det = E.det * O.det
  calc
    M.det = (M.submatrix g g).det := (Matrix.det_submatrix_equiv_self g M).symm
    _ = (Matrix.fromBlocks E 0 0 O).det := by rw [hR]
    _ = E.det * O.det := Matrix.det_fromBlocks_zero₂₁ E 0 O

#print axioms c2_six_parity_determinant
end GeometryOfNumbers.Analysis
