import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-! One scalar reciprocal reduction of a finite positive resolvent.
The factor can be rectangular. No square root, spectral fit, or positive
lower bound on its singular values is required. -/

namespace CarryRadialReduction

open Matrix
open scoped Matrix
noncomputable section
set_option autoImplicit false

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- Orthogonal complement of the current vector, expressed without a square root. -/
def complement (v : n → ℝ) : Matrix n n ℝ :=
  1 - (v ⬝ᵥ v)⁻¹ • vecMulVec v v

theorem complement_mulVec (v x : n → ℝ) :
    complement v *ᵥ x = x - ((v ⬝ᵥ x) / (v ⬝ᵥ v)) • v := by
  rw [complement, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec]
  ext i
  change x i - (v ⬝ᵥ v)⁻¹ * (v i * (v ⬝ᵥ x)) = x i - ((v ⬝ᵥ x) / (v ⬝ᵥ v)) * v i
  rw [div_eq_mul_inv]
  ring

theorem complement_transpose (v : n → ℝ) :
    (complement v)ᵀ = complement v := by
  ext i j
  simp [complement, vecMulVec_apply, Matrix.one_apply, eq_comm, mul_comm]

theorem complement_idempotent (v : n → ℝ) (ha : v ⬝ᵥ v ≠ 0) :
    complement v * complement v = complement v := by
  have ho : vecMulVec v ((v ⬝ᵥ v) • v) = (v ⬝ᵥ v) • vecMulVec v v := by
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  unfold complement
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_smul, Matrix.smul_mul, vecMulVec_mul_vecMulVec, ho]
  simp only [smul_smul, inv_mul_cancel₀ ha, mul_one]
  abel

variable [DecidableEq m]

/-- The compressed factor is rectangular in the reverse direction. -/
def reducedFactor (B : Matrix m n ℝ) (v : n → ℝ) : Matrix n m ℝ :=
  complement v * Bᵀ

omit [Fintype m] [DecidableEq m] in
theorem reducedFactor_gram (B : Matrix m n ℝ) (v : n → ℝ)
    (ha : v ⬝ᵥ v ≠ 0) :
    (reducedFactor B v)ᵀ * reducedFactor B v = B * complement v * Bᵀ := by
  rw [reducedFactor, transpose_mul, transpose_transpose, complement_transpose,
    Matrix.mul_assoc, ← Matrix.mul_assoc (complement v), complement_idempotent v ha,
    ← Matrix.mul_assoc]

omit [DecidableEq n] [DecidableEq m] in
private theorem dot_transpose_mulVec (B : Matrix m n ℝ) (v : n → ℝ) (y : m → ℝ) :
    v ⬝ᵥ (Bᵀ *ᵥ y) = (B *ᵥ v) ⬝ᵥ y := by
  rw [dotProduct_mulVec, vecMul_transpose]

/-- Resolvent reduction in scalar form. The equation is cleared of scalar
denominators. In a neighborhood of zero, both matrix equations have unique
solutions and the equality is the reciprocal reduction of the readout. -/
theorem reciprocalReduction_resolvents (B : Matrix m n ℝ) (v x : n → ℝ) (y : m → ℝ)
    (s : ℝ) (ha : v ⬝ᵥ v ≠ 0)
    (hx : (1 - s • (Bᵀ * B)) *ᵥ x = v)
    (hy : (1 - s • (B * complement v * Bᵀ)) *ᵥ y = B *ᵥ v)
    (hinj : Function.Injective (fun z => (1 - s • (B * complement v * Bᵀ)) *ᵥ z)) :
    (v ⬝ᵥ v) * ((v ⬝ᵥ x) - (v ⬝ᵥ v)) =
      s * (v ⬝ᵥ x) * ((B *ᵥ v) ⬝ᵥ y) := by
  have hvx : x - s • (Bᵀ *ᵥ (B *ᵥ x)) = v := by
    simpa only [sub_mulVec, one_mulVec, smul_mulVec, mulVec_mulVec] using hx
  have hdot : (v ⬝ᵥ x) - s * ((B *ᵥ v) ⬝ᵥ (B *ᵥ x)) = (v ⬝ᵥ v) := by
    simpa only [dotProduct_sub, dotProduct_smul, smul_eq_mul, dot_transpose_mulVec] using
      congrArg (fun z => v ⬝ᵥ z) hvx
  have hAx : B *ᵥ x - s • (B *ᵥ (Bᵀ *ᵥ (B *ᵥ x))) = B *ᵥ v := by
    simpa only [mulVec_sub, mulVec_smul] using congrArg (fun z => B *ᵥ z) hvx
  have hBx : B *ᵥ x = ((v ⬝ᵥ x) / (v ⬝ᵥ v)) • y := by
    apply hinj
    change (1 - s • (B * complement v * Bᵀ)) *ᵥ (B *ᵥ x) =
      (1 - s • (B * complement v * Bᵀ)) *ᵥ (((v ⬝ᵥ x) / (v ⬝ᵥ v)) • y)
    rw [mulVec_smul, hy]
    simp only [sub_mulVec, one_mulVec, smul_mulVec, ← mulVec_mulVec,
      complement_mulVec, dot_transpose_mulVec, mulVec_sub, mulVec_smul]
    ext i
    have hAi := congrFun hAx i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hAi ⊢
    field_simp
    linear_combination (v ⬝ᵥ v) * hAi - (B *ᵥ v) i * hdot
  have hnorm : (B *ᵥ v) ⬝ᵥ (B *ᵥ x) =
      ((v ⬝ᵥ x) / (v ⬝ᵥ v)) * ((B *ᵥ v) ⬝ᵥ y) := by
    rw [hBx, dotProduct_smul, smul_eq_mul]
  rw [hnorm] at hdot
  field_simp at hdot
  linear_combination hdot

omit [DecidableEq n] [DecidableEq m] in
/-- Coefficient of degree one of a positive resolvent is a Gram square. -/
theorem firstCoefficient_eq_square (B : Matrix m n ℝ) (v : n → ℝ) :
    v ⬝ᵥ ((Bᵀ * B) *ᵥ v) = (B *ᵥ v) ⬝ᵥ (B *ᵥ v) := by
  rw [← mulVec_mulVec, dot_transpose_mulVec]

omit [DecidableEq n] [DecidableEq m] in
theorem firstCoefficient_pos_iff (B : Matrix m n ℝ) (v : n → ℝ) :
    0 < v ⬝ᵥ ((Bᵀ * B) *ᵥ v) ↔ B *ᵥ v ≠ 0 := by
  rw [firstCoefficient_eq_square]
  constructor
  · intro hp hz
    simp [hz] at hp
  · intro hn
    have hnn : 0 ≤ (B *ᵥ v) ⬝ᵥ (B *ᵥ v) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg ((B *ᵥ v) i)
    exact lt_of_le_of_ne hnn (fun he => hn (dotProduct_self_eq_zero.mp he.symm))

omit [DecidableEq m] in
/-- The new derivative is strict precisely when the old energy image
has a component orthogonal to the old vector. -/
theorem reducedFirstCoefficient_pos_iff (B : Matrix m n ℝ) (v : n → ℝ)
    (ha : v ⬝ᵥ v ≠ 0) :
    let v' := (v ⬝ᵥ v)⁻¹ • (B *ᵥ v)
    0 < v' ⬝ᵥ (((reducedFactor B v)ᵀ * reducedFactor B v) *ᵥ v') ↔
      complement v *ᵥ ((Bᵀ * B) *ᵥ v) ≠ 0 := by
  dsimp only
  rw [firstCoefficient_pos_iff]
  simp only [reducedFactor, ← mulVec_mulVec, mulVec_smul]
  constructor
  · intro hp hz
    exact hp (by rw [hz, smul_zero])
  · intro hp
    exact smul_ne_zero (inv_ne_zero ha) hp

#print axioms reducedFirstCoefficient_pos_iff

#print axioms reducedFactor_gram
#print axioms reciprocalReduction_resolvents
#print axioms firstCoefficient_pos_iff

end
end CarryRadialReduction
