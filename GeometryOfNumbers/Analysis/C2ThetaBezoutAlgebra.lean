import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
Finite and all-order algebra underlying the C2 theta-Bézout route.
These are universally quantified algebraic identities.  The source
integral-to-Taylor-coefficient identification is a separate obligation.
-/

namespace GeometryOfNumbers.Analysis

noncomputable section

/-- Coefficient convolution by a raw characteristic `W(X)=sum w_k X^k`. -/
def c2ThetaToeplitz (n : ℕ) (w : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j ≤ i then w (i.val - j.val) else 0

/-- Either of the two canonical (parity-shifted) moment Hankel blocks. -/
def c2ThetaHankel (n shift : ℕ) (h : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => h (i.val + j.val + shift)

/-- The actual double coefficient convolution of `W(U)W(V)` with the
formal divided-difference kernel of `-W'/W`.  This is the coefficient-side
Bézout block, *before* any elimination or division by a matrix pivot. -/
def c2ThetaBezoutConvolution (n shift : ℕ) (w h : ℕ → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ a : Fin n, ∑ b : Fin n,
    c2ThetaToeplitz n w i a * h (a.val + b.val + shift) *
    c2ThetaToeplitz n w j b

/-- The all-order Bézout/Hankel matrix congruence on raw Taylor coefficients,
including every crossed entry. -/
theorem c2ThetaBezoutConvolution_eq_congruence
    (n shift : ℕ) (w h : ℕ → ℝ) :
    c2ThetaBezoutConvolution n shift w h =
      c2ThetaToeplitz n w * c2ThetaHankel n shift h *
        (c2ThetaToeplitz n w).transpose := by
  ext i j
  simp only [c2ThetaBezoutConvolution, Matrix.mul_apply,
    Matrix.transpose_apply, c2ThetaHankel]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The coefficient convolution matrix is lower-triangular. -/
theorem c2ThetaToeplitz_lowerTriangular (n : ℕ) (w : ℕ → ℝ) :
    (c2ThetaToeplitz n w).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have h : ¬ j ≤ i := by
    exact not_le.mpr hij
  simp [c2ThetaToeplitz, h]

/-- Its determinant is a pure power of the value of the raw characteristic
at the center. -/
theorem c2ThetaToeplitz_det (n : ℕ) (w : ℕ → ℝ) :
    (c2ThetaToeplitz n w).det = (w 0) ^ n := by
  rw [Matrix.det_of_lowerTriangular _ (c2ThetaToeplitz_lowerTriangular n w)]
  simp [c2ThetaToeplitz]

/-- Exact determinant transport, no inverse or Schur complement. -/
theorem c2ThetaBezoutConvolution_det
    (n shift : ℕ) (w h : ℕ → ℝ) :
    (c2ThetaBezoutConvolution n shift w h).det =
      (w 0) ^ (2 * n) * (c2ThetaHankel n shift h).det := by
  rw [c2ThetaBezoutConvolution_eq_congruence,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    c2ThetaToeplitz_det]
  ring

/-- Positivity can be transferred from a canonical Hankel block to its
Bézout coefficient block without additional analytic assumptions. -/
theorem c2ThetaBezoutConvolution_posSemidef
    (n shift : ℕ) (w h : ℕ → ℝ)
    (hh : (c2ThetaHankel n shift h).PosSemidef) :
    (c2ThetaBezoutConvolution n shift w h).PosSemidef := by
  rw [c2ThetaBezoutConvolution_eq_congruence,
    ← Matrix.conjTranspose_eq_transpose_of_trivial (c2ThetaToeplitz n w)]
  exact hh.mul_mul_conjTranspose_same (c2ThetaToeplitz n w)

/-- Nonzero central characteristic makes every finite coefficient
convolution invertible. -/
theorem c2ThetaToeplitz_isUnit
    (n : ℕ) (w : ℕ → ℝ) (hw : w 0 ≠ 0) :
    IsUnit (c2ThetaToeplitz n w) := by
  apply (Matrix.isUnit_iff_isUnit_det (c2ThetaToeplitz n w)).mpr
  rw [c2ThetaToeplitz_det]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hw)

/-- Strict positivity transports in either parity block, provided `W(0)≠0`. -/
theorem c2ThetaBezoutConvolution_posDef
    (n shift : ℕ) (w h : ℕ → ℝ) (hw : w 0 ≠ 0)
    (hh : (c2ThetaHankel n shift h).PosDef) :
    (c2ThetaBezoutConvolution n shift w h).PosDef := by
  rw [c2ThetaBezoutConvolution_eq_congruence,
    ← Matrix.conjTranspose_eq_transpose_of_trivial (c2ThetaToeplitz n w)]
  apply hh.mul_mul_conjTranspose_same
  exact Matrix.vecMul_injective_iff_isUnit.mpr (c2ThetaToeplitz_isUnit n w hw)

/-- When the raw characteristic does not vanish at the center, the
Bézout and completed Hankel blocks have exactly the same positive-definite
status at *every* finite size; this is not a proof that either is positive. -/
theorem c2ThetaBezoutConvolution_posDef_iff
    (n shift : ℕ) (w h : ℕ → ℝ) (hw : w 0 ≠ 0) :
    (c2ThetaBezoutConvolution n shift w h).PosDef ↔
      (c2ThetaHankel n shift h).PosDef := by
  rw [c2ThetaBezoutConvolution_eq_congruence,
    ← Matrix.conjTranspose_eq_transpose_of_trivial (c2ThetaToeplitz n w)]
  simpa only [Matrix.star_eq_conjTranspose] using
    (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (c2ThetaToeplitz_isUnit n w hw))

/-- The adjacent determinant ratio (the Schur pivot whenever the previous
head is invertible) changes by exactly the square of `W(0)`, in every degree.
No hypothesis about signs or locations of zeros is used. -/
theorem c2ThetaBezoutConvolution_adjacent_det_ratio
    (n shift : ℕ) (w h : ℕ → ℝ) (hw : w 0 ≠ 0)
    (hhead : (c2ThetaHankel n shift h).det ≠ 0) :
    (c2ThetaBezoutConvolution (n+1) shift w h).det /
      (c2ThetaBezoutConvolution n shift w h).det =
    (w 0)^2 * ((c2ThetaHankel (n+1) shift h).det /
      (c2ThetaHankel n shift h).det) := by
  rw [c2ThetaBezoutConvolution_det, c2ThetaBezoutConvolution_det]
  have hw2 : (w 0) ^ (2*n) ≠ 0 := pow_ne_zero _ hw
  field_simp [hw2, hhead]
  ring

/-- The first even Bézout coefficient follows from the native logarithmic
relation `W H = - W'`, without dividing by the characteristic. -/
theorem c2ThetaBezout_even_origin
    (w h : ℕ → ℝ) (h0 : w 0 * h 0 = -w 1) :
    (c2ThetaBezoutConvolution 1 0 w h) 0 0 = -w 0 * w 1 := by
  simp [c2ThetaBezoutConvolution, c2ThetaToeplitz] at *
  nlinarith [congrArg (fun x : ℝ => w 0 * x) h0]

/-- The first odd Bézout coefficient reads the second raw Taylor
coefficient; its sign does not follow from positivity of the density alone. -/
theorem c2ThetaBezout_odd_origin
    (w h : ℕ → ℝ)
    (h0 : w 0 * h 0 = -w 1)
    (h1 : w 0 * h 1 + w 1 * h 0 = -(2 : ℝ) * w 2) :
    (c2ThetaBezoutConvolution 1 1 w h) 0 0 =
      (w 1)^2 - 2 * w 0 * w 2 := by
  simp [c2ThetaBezoutConvolution, c2ThetaToeplitz] at *
  nlinarith [congrArg (fun x : ℝ => w 1 * x) h0,
    congrArg (fun x : ℝ => w 0 * x) h1]

/-- First no-division Bézout numerator: `W'=-WH` is the only hypothesis.
No positivity, camera or zero-location information is presumed. -/
theorem c2ThetaBezout_even_numerator
    (u v Wu Wv Du Dv Hu Hv : ℝ)
    (hDu : Du = -Wu * Hu) (hDv : Dv = -Wv * Hv) :
    v * Wu * Dv - u * Du * Wv =
      Wu * Wv * (u * Hu - v * Hv) := by
  rw [hDu, hDv]
  ring

/-- Second no-division Bézout numerator, for the shifted Hankel sector. -/
theorem c2ThetaBezout_odd_numerator
    (Wu Wv Du Dv Hu Hv : ℝ)
    (hDu : Du = -Wu * Hu) (hDv : Dv = -Wv * Hv) :
    Wu * Dv - Du * Wv = Wu * Wv * (Hu - Hv) := by
  rw [hDu, hDv]
  ring

end
end GeometryOfNumbers.Analysis

#print axioms GeometryOfNumbers.Analysis.c2ThetaBezoutConvolution_eq_congruence
#print axioms GeometryOfNumbers.Analysis.c2ThetaBezoutConvolution_det
#print axioms GeometryOfNumbers.Analysis.c2ThetaBezoutConvolution_posDef

#print axioms GeometryOfNumbers.Analysis.c2ThetaBezoutConvolution_posDef_iff
#print axioms GeometryOfNumbers.Analysis.c2ThetaBezoutConvolution_adjacent_det_ratio
