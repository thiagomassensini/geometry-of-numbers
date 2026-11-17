import GeometryOfNumbers.Analysis.CarryMaterialPickSixParity
import Mathlib.Tactic

/-! Exact reindexing of 7×7 confluent Cauchy--Pick response
into the even native Hankel H4 and shifted odd Hankel K3.
No sign is assumed. -/
namespace GeometryOfNumbers.Analysis
open scoped Matrix

noncomputable def sevenParityReindex : (Fin 4 ⊕ Fin 3) ≃ Fin 7 :=
  Equiv.ofBijective
    (fun x => match x with
      | Sum.inl i => (⟨2*i.val, by omega⟩ : Fin 7)
      | Sum.inr j => (⟨2*j.val+1, by omega⟩ : Fin 7))
    (by decide)

theorem c2_seven_parity_determinant (a b c d e f g : ℂ) :
    (!![a, 0, b, 0, c, 0, d;
        0, b, 0, c, 0, d, 0;
        b, 0, c, 0, d, 0, e;
        0, c, 0, d, 0, e, 0;
        c, 0, d, 0, e, 0, f;
        0, d, 0, e, 0, f, 0;
        d, 0, e, 0, f, 0, g] : Matrix (Fin 7) (Fin 7) ℂ).det =
      (!![a,b,c,d;b,c,d,e;c,d,e,f;d,e,f,g] : Matrix (Fin 4) (Fin 4) ℂ).det *
      (!![b,c,d;c,d,e;d,e,f] : Matrix (Fin 3) (Fin 3) ℂ).det := by
  let M : Matrix (Fin 7) (Fin 7) ℂ :=
    !![a, 0, b, 0, c, 0, d;
       0, b, 0, c, 0, d, 0;
       b, 0, c, 0, d, 0, e;
       0, c, 0, d, 0, e, 0;
       c, 0, d, 0, e, 0, f;
       0, d, 0, e, 0, f, 0;
       d, 0, e, 0, f, 0, g]
  let E : Matrix (Fin 4) (Fin 4) ℂ := !![a,b,c,d;b,c,d,e;c,d,e,f;d,e,f,g]
  let O : Matrix (Fin 3) (Fin 3) ℂ := !![b,c,d;c,d,e;d,e,f]
  let q := sevenParityReindex
  have hR : M.submatrix q q = Matrix.fromBlocks E 0 0 O := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [M,E,O,q,sevenParityReindex,Matrix.fromBlocks]
  change M.det = E.det * O.det
  calc
    M.det = (M.submatrix q q).det := (Matrix.det_submatrix_equiv_self q M).symm
    _ = (Matrix.fromBlocks E 0 0 O).det := by rw [hR]
    _ = E.det * O.det := Matrix.det_fromBlocks_zero₂₁ E 0 O

#print axioms c2_seven_parity_determinant
end GeometryOfNumbers.Analysis
