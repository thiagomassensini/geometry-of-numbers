import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic

namespace C3Cofactor

noncomputable section
set_option autoImplicit false

def oddThirdB (a b d e f g : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a, b, e; b, d, f; e, f, g]

def oddPrefixDet (a b d : ℝ) : ℝ := a * d - b ^ 2

def oddResidual0 (a b e x y : ℝ) : ℝ := a * x + b * y + e

def oddResidual1 (b d f x y : ℝ) : ℝ := b * x + d * y + f

def oddDirectionEnergy (a b d e f g x y : ℝ) : ℝ :=
  a * x ^ 2 + 2 * b * x * y + d * y ^ 2 + 2 * e * x + 2 * f * y + g

def oddAdjugateResidual (a b d e f x y : ℝ) : ℝ :=
  d * oddResidual0 a b e x y ^ 2 -
    2 * b * oddResidual0 a b e x y * oddResidual1 b d f x y +
      a * oddResidual1 b d f x y ^ 2

/-- The exact cofactorial identity for a symmetric 3×3 bordered matrix. It is
valid with no non-singularity assumption on the 2×2 prefix. -/
theorem odd_third_cofactor_identity
    (a b d e f g x y : ℝ) :
    (oddThirdB a b d e f g).det =
      oddPrefixDet a b d * oddDirectionEnergy a b d e f g x y -
        oddAdjugateResidual a b d e f x y := by
  simp [oddThirdB, oddPrefixDet, oddDirectionEnergy, oddAdjugateResidual,
    oddResidual0, oddResidual1, Matrix.det_fin_three]
  ring

/-- The canonical cofactor vector has the determinant in its last coordinate,
and its image under the bordered matrix is the last-coordinate determinant
vector. This is the 3×3 specialization of `B w = (0,…,det B)`. -/
theorem odd_third_cofactor_vector_identity
    (a b d e f g : ℝ) :
    (oddThirdB a b d e f g).mulVec
        (![b * f - d * e, b * e - a * f, oddPrefixDet a b d] : Fin 3 → ℝ) =
      (![0, 0, (oddThirdB a b d e f g).det] : Fin 3 → ℝ) := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, oddThirdB, oddPrefixDet,
      Matrix.det_fin_three, Fin.sum_univ_succ] <;> ring

/-- The cofactor vector's quadratic form is the leading determinant times the
full determinant; this remains true when that leading determinant vanishes. -/
theorem odd_third_cofactor_vector_quadratic
    (a b d e f g : ℝ) :
    (![b * f - d * e, b * e - a * f, oddPrefixDet a b d] : Fin 3 → ℝ) ⬝ᵥ
        ((oddThirdB a b d e f g).mulVec
          (![b * f - d * e, b * e - a * f, oddPrefixDet a b d] : Fin 3 → ℝ)) =
      oddPrefixDet a b d * (oddThirdB a b d e f g).det := by
  rw [odd_third_cofactor_vector_identity]
  simp [dotProduct, oddPrefixDet, Fin.sum_univ_succ]

#print axioms odd_third_cofactor_identity
#print axioms odd_third_cofactor_vector_identity
#print axioms odd_third_cofactor_vector_quadratic

end
end C3Cofactor
