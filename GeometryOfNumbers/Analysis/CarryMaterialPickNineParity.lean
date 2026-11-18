import GeometryOfNumbers.Analysis.CarryMaterialPickEightParity
import Mathlib.Tactic

/-! Exact determinant parity of the nine-point confluent Green source.
The simultaneous permutation retains every one of the 81 crossings. -/
namespace GeometryOfNumbers.Analysis
open scoped Matrix

noncomputable def nineParityReindex : (Fin 5 ⊕ Fin 4) ≃ Fin 9 :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl i => (⟨2*i.val, by omega⟩ : Fin 9)
      | Sum.inr j => (⟨2*j.val+1, by omega⟩ : Fin 9))
    (by decide)

theorem c2_nine_parity_determinant (a b c d e f g h i : ℂ) :
    (!![a, 0, b, 0, c, 0, d, 0, e;
        0, b, 0, c, 0, d, 0, e, 0;
        b, 0, c, 0, d, 0, e, 0, f;
        0, c, 0, d, 0, e, 0, f, 0;
        c, 0, d, 0, e, 0, f, 0, g;
        0, d, 0, e, 0, f, 0, g, 0;
        d, 0, e, 0, f, 0, g, 0, h;
        0, e, 0, f, 0, g, 0, h, 0;
        e, 0, f, 0, g, 0, h, 0, i] : Matrix (Fin 9) (Fin 9) ℂ).det =
      (!![a,b,c,d,e;b,c,d,e,f;c,d,e,f,g;d,e,f,g,h;e,f,g,h,i] : Matrix (Fin 5) (Fin 5) ℂ).det *
      (!![b,c,d,e;c,d,e,f;d,e,f,g;e,f,g,h] : Matrix (Fin 4) (Fin 4) ℂ).det := by
  let M : Matrix (Fin 9) (Fin 9) ℂ := !![a, 0, b, 0, c, 0, d, 0, e;
        0, b, 0, c, 0, d, 0, e, 0;
        b, 0, c, 0, d, 0, e, 0, f;
        0, c, 0, d, 0, e, 0, f, 0;
        c, 0, d, 0, e, 0, f, 0, g;
        0, d, 0, e, 0, f, 0, g, 0;
        d, 0, e, 0, f, 0, g, 0, h;
        0, e, 0, f, 0, g, 0, h, 0;
        e, 0, f, 0, g, 0, h, 0, i]
  let E : Matrix (Fin 5) (Fin 5) ℂ := !![a,b,c,d,e;b,c,d,e,f;c,d,e,f,g;d,e,f,g,h;e,f,g,h,i]
  let O : Matrix (Fin 4) (Fin 4) ℂ := !![b,c,d,e;c,d,e,f;d,e,f,g;e,f,g,h]
  let q := nineParityReindex
  have hR : M.submatrix q q = Matrix.fromBlocks E 0 0 O := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [M,E,O,q,nineParityReindex,Matrix.fromBlocks]
  change M.det = E.det * O.det
  calc
    M.det = (M.submatrix q q).det := (Matrix.det_submatrix_equiv_self q M).symm
    _ = (Matrix.fromBlocks E 0 0 O).det := by rw [hR]
    _ = E.det * O.det := Matrix.det_fromBlocks_zero₂₁ E 0 O

#print axioms c2_nine_parity_determinant
end GeometryOfNumbers.Analysis
