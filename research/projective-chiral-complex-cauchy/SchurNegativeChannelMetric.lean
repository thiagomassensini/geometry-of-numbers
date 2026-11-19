import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# The negative-channel metric forced by signed Schur elimination

The prefix is the only signed block required to be invertible. Neither the
new Schur block nor any domination of the new returned channel is assumed.
-/

namespace CarrySchurChannels

open Matrix
open scoped Matrix ComplexOrder
noncomputable section
set_option autoImplicit false

variable {p q m n : Type*} [Fintype p] [Fintype q] [Fintype m]
  [DecidableEq m] [DecidableEq q]

/-- The weight on the original returned channel after eliminating the prefix. -/
def negativeMetric (P : Matrix m m ℂ) (B₀ : Matrix q m ℂ) : Matrix q q ℂ :=
  1 + B₀ * P⁻¹ * B₀ᴴ

/-- All ordered crossings of the reduced signed form. The new columns are
already orthogonal to the prefix in the positive channel. The old negative
crossings therefore enter the Schur complement with a definite minus sign. -/
theorem schur_eq_weighted_negative_of_positive_orthogonal
    (A₀ : Matrix p m ℂ) (B₀ : Matrix q m ℂ)
    (A : Matrix p n ℂ) (B : Matrix q n ℂ)
    (horth : A₀ᴴ * A = 0) :
    let P := A₀ᴴ * A₀ - B₀ᴴ * B₀
    (Aᴴ * A - Bᴴ * B) - (Aᴴ * A₀ - Bᴴ * B₀) * P⁻¹ * (A₀ᴴ * A - B₀ᴴ * B) =
      Aᴴ * A - Bᴴ * negativeMetric P B₀ * B := by
  have horth' : Aᴴ * A₀ = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose horth
  dsimp only
  rw [horth, horth', zero_sub, zero_sub]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  unfold negativeMetric
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, ← sub_sub]
  simp only [Matrix.mul_assoc]

omit [Fintype q] [DecidableEq q] in
/-- The actual positive-channel projection is one admissible prefix
subtraction. Invertibility of the positive Gram follows from a positive
signed prefix. -/
theorem positiveChannel_subtraction_orthogonal (A₀ : Matrix p m ℂ)
    (A : Matrix p n ℂ) (h : IsUnit (A₀ᴴ * A₀).det) :
    A₀ᴴ * (A - A₀ * ((A₀ᴴ * A₀)⁻¹ * (A₀ᴴ * A))) = 0 := by
  rw [Matrix.mul_sub, ← Matrix.mul_assoc A₀ᴴ A₀,
    Matrix.mul_nonsing_inv_cancel_left _ _ h, sub_self]

omit [Fintype p] [Fintype q] [DecidableEq q] in
/-- Subtracting any old combination from each new column leaves the true
signed Schur complement invariant. This justifies positive-channel
orthogonalization before applying the previous identity. -/
theorem schur_invariant_under_prefix_subtraction
    (P : Matrix m m ℂ) (C : Matrix m n ℂ) (D : Matrix n n ℂ)
    (L : Matrix m n ℂ) (hP : P.IsHermitian) (hu : IsUnit P.det) :
    (D - Lᴴ * C - Cᴴ * L + Lᴴ * P * L) -
      (C - P * L)ᴴ * P⁻¹ * (C - P * L) =
      D - Cᴴ * P⁻¹ * C := by
  have hrl : (Cᴴ * P⁻¹) * P = Cᴴ := Matrix.nonsing_inv_mul_cancel_right P Cᴴ hu
  have hlr : (Lᴴ * P) * P⁻¹ = Lᴴ := Matrix.mul_nonsing_inv_cancel_right P Lᴴ hu
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hP.eq, Matrix.sub_mul,
    hlr, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    ← Matrix.mul_assoc (Cᴴ * P⁻¹) P L, hrl, ← Matrix.mul_assoc Lᴴ P L]
  abel

omit [Fintype p] in
/-- The negative metric is an inverse complement for the prefix graph. -/
theorem negativeMetric_eq_inverse (G P : Matrix m m ℂ)
    (B₀ : Matrix q m ℂ) (hG : IsUnit G) (hP : IsUnit P)
    (h : P = G - B₀ᴴ * B₀) :
    negativeMetric P B₀ = (1 - B₀ * G⁻¹ * B₀ᴴ)⁻¹ := by
  have hGinv : IsUnit G⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hG
  have hGii : (G⁻¹)⁻¹ = G := Matrix.nonsing_inv_nonsing_inv G
    ((Matrix.isUnit_iff_isUnit_det G).mp hG)
  have hC : IsUnit (-G⁻¹) := hGinv.neg
  have hn (X : Matrix m m ℂ) (hX : IsUnit X) : (-X)⁻¹ = -X⁻¹ := by
    apply Matrix.inv_eq_left_inv
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    exact Matrix.nonsing_inv_mul X ((Matrix.isUnit_iff_isUnit_det X).mp hX)
  have he : (-G⁻¹)⁻¹ + B₀ᴴ * (1 : Matrix q q ℂ)⁻¹ * B₀ = -P := by
    rw [hn G⁻¹ hGinv, hGii, inv_one, Matrix.mul_one, h]
    abel
  have hh := Matrix.add_mul_mul_inv_eq_sub (1 : Matrix q q ℂ) B₀ (-G⁻¹) B₀ᴴ
    isUnit_one hC (by rw [he]; exact hP.neg)
  rw [he] at hh
  simpa only [negativeMetric, inv_one, Matrix.one_mul, Matrix.mul_one,
    hn P hP, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add, sub_eq_add_neg, neg_neg]
    using hh.symm

omit [Fintype p] in
/-- The added negative-channel cost is positive semidefinite on a positive
prefix. This conclusion concerns the weight, not the next Schur sign. -/
theorem negativeMetric_sub_one_posSemidef (P : Matrix m m ℂ)
    (B₀ : Matrix q m ℂ) (hp : P.PosDef) :
    (negativeMetric P B₀ - 1).PosSemidef := by
  unfold negativeMetric
  rw [add_sub_cancel_left]
  simpa only [Matrix.conjTranspose_conjTranspose] using
    (hp.inv.posSemidef.mul_mul_conjTranspose_same B₀)

/-- On the two-node radial Cauchy Gram at step one, choose the synthetic
multipliers 3/4 and 1/2. Positive-channel projection has cost 1/36,
the ordinary negative norm is 1/48, and the prefix crossing adds 1/56.
The full Schur margin has the opposite sign from the unweighted margin. -/
theorem cauchy_twoPoint_naive_pos_true_neg :
    (0 : ℝ) < (1/4 - (1/3)^2/(1/2)) -
      ((1/2)^2*(1/4) - 2*(2/3)*(3/4)*(1/2)*(1/3) + (2/3)^2*(3/4)^2*(1/2)) ∧
    (3/16 : ℝ) - (5/24)^2/(7/32) = -11/1008 := by
  norm_num

#print axioms schur_eq_weighted_negative_of_positive_orthogonal
#print axioms schur_invariant_under_prefix_subtraction
#print axioms negativeMetric_eq_inverse
#print axioms negativeMetric_sub_one_posSemidef

end
end CarrySchurChannels
