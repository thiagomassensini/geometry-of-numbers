import CofactorIdentity
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace C3Cofactor

noncomputable section
set_option autoImplicit false

def oddQuadratic (a b d e f g x y z : ℝ) : ℝ :=
  a * x ^ 2 + 2 * b * x * y + 2 * e * x * z + d * y ^ 2 +
    2 * f * y * z + g * z ^ 2

/-- The ordinary quadratic form represented by the symmetric 3×3 border. -/
theorem oddThirdB_quadratic_form
    (a b d e f g x y z : ℝ) :
    dotProduct (![x, y, z] : Fin 3 → ℝ) ((oddThirdB a b d e f g).mulVec
      (![x, y, z] : Fin 3 → ℝ)) = oddQuadratic a b d e f g x y z := by
  simp [dotProduct, Matrix.mulVec, oddThirdB, oddQuadratic, Fin.sum_univ_succ]
  ring

/-- Exact completion of squares using the first two leading principal minors. -/
theorem oddThirdB_complete_square
    (a b d e f g x y z : ℝ)
    (ha : a ≠ 0) (hD : oddPrefixDet a b d ≠ 0) :
    oddQuadratic a b d e f g x y z =
      a * (x + (b * y + e * z) / a) ^ 2 +
        (oddPrefixDet a b d / a) *
          (y + (a * f - b * e) * z / oddPrefixDet a b d) ^ 2 +
        ((oddThirdB a b d e f g).det / oddPrefixDet a b d) * z ^ 2 := by
  have hD' : a * d - b ^ 2 ≠ 0 := by simpa [oddPrefixDet] using hD
  rw [Matrix.det_fin_three]
  simp [oddThirdB, oddQuadratic, oddPrefixDet]
  field_simp [ha, hD']
  ring

/-- A strict cofactorial margin plus positive leading minors makes the full
odd 3×3 Bézout block positive definite. The result is conditional and does
not manufacture the source inequality. -/
theorem odd_third_posDef_of_cofactor_gate
    (a b d e f g x y : ℝ)
    (ha : 0 < a)
    (hD : 0 < oddPrefixDet a b d)
    (hgate : 0 < oddPrefixDet a b d * oddDirectionEnergy a b d e f g x y -
      oddAdjugateResidual a b d e f x y) :
    (oddThirdB a b d e f g).PosDef := by
  have hdet : 0 < (oddThirdB a b d e f g).det := by
    rw [odd_third_cofactor_identity]
    exact hgate
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hD0 : oddPrefixDet a b d ≠ 0 := ne_of_gt hD
  have hHerm : (oddThirdB a b d e f g).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [oddThirdB]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm ?_
  intro v hv
  let X := v 0
  let Y := v 1
  let Z := v 2
  have hv_eq : v = ![X, Y, Z] := by
    ext i
    fin_cases i <;> rfl
  rw [hv_eq] at hv ⊢
  change 0 < dotProduct (![X, Y, Z] : Fin 3 → ℝ)
    ((oddThirdB a b d e f g).mulVec (![X, Y, Z] : Fin 3 → ℝ))
  rw [oddThirdB_quadratic_form, oddThirdB_complete_square a b d e f g X Y Z ha0 hD0]
  let q₁ := X + (b * Y + e * Z) / a
  let q₂ := Y + (a * f - b * e) * Z / oddPrefixDet a b d
  have hn₁ : 0 ≤ a * q₁ ^ 2 := mul_nonneg (le_of_lt ha) (sq_nonneg q₁)
  have hn₂ : 0 ≤ (oddPrefixDet a b d / a) * q₂ ^ 2 :=
    mul_nonneg (le_of_lt (div_pos hD ha)) (sq_nonneg q₂)
  by_cases hZ : Z ≠ 0
  · have hp₃ : 0 < ((oddThirdB a b d e f g).det / oddPrefixDet a b d) * Z ^ 2 :=
      mul_pos (div_pos hdet hD) (sq_pos_of_ne_zero hZ)
    change 0 < a * q₁ ^ 2 +
      (oddPrefixDet a b d / a) * q₂ ^ 2 +
        ((oddThirdB a b d e f g).det / oddPrefixDet a b d) * Z ^ 2
    linarith
  · have hZeq : Z = 0 := by simpa using hZ
    by_cases hY : Y ≠ 0
    · have hq₂ : q₂ = Y := by simp [q₂, hZeq]
      have hp₂ : 0 < (oddPrefixDet a b d / a) * q₂ ^ 2 := by
        rw [hq₂]
        exact mul_pos (div_pos hD ha) (sq_pos_of_ne_zero hY)
      change 0 < a * q₁ ^ 2 +
        (oddPrefixDet a b d / a) * q₂ ^ 2 +
          ((oddThirdB a b d e f g).det / oddPrefixDet a b d) * Z ^ 2
      have hn₃ : 0 ≤ ((oddThirdB a b d e f g).det / oddPrefixDet a b d) * Z ^ 2 :=
        mul_nonneg (le_of_lt (div_pos hdet hD)) (sq_nonneg Z)
      linarith
    · have hYeq : Y = 0 := by simpa using hY
      have hX : X ≠ 0 := by
        intro hX0
        apply hv
        ext i
        fin_cases i <;> simp [hX0, hYeq, hZeq]
      have hq₁ : q₁ = X := by simp [q₁, hYeq, hZeq]
      have hp₁ : 0 < a * q₁ ^ 2 := by
        rw [hq₁]
        exact mul_pos ha (sq_pos_of_ne_zero hX)
      have hn₃ : 0 ≤ ((oddThirdB a b d e f g).det / oddPrefixDet a b d) * Z ^ 2 :=
        mul_nonneg (le_of_lt (div_pos hdet hD)) (sq_nonneg Z)
      change 0 < a * q₁ ^ 2 +
        (oddPrefixDet a b d / a) * q₂ ^ 2 +
          ((oddThirdB a b d e f g).det / oddPrefixDet a b d) * Z ^ 2
      linarith

#print axioms oddThirdB_quadratic_form
#print axioms oddThirdB_complete_square
#print axioms odd_third_posDef_of_cofactor_gate

end
end C3Cofactor
