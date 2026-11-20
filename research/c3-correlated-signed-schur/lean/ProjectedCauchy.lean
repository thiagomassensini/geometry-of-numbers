import Mathlib

/-!
Cauchy–Schwarz from the exact prior PSD prefix, for mixed source pair.
No auxiliary positive Gram is introduced.
-/
namespace TiltSchurProjectedCS
open Matrix
noncomputable section
set_option maxHeartbeats 1200000

def pair {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ y)

theorem pair_sym {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.transpose = M) (x y : Fin n → ℝ) :
    pair M x y = pair M y x := by
  unfold pair
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM, dotProduct_comm]

theorem projected_cs {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.PosSemidef) (hSym : M.transpose = M)
    (x y : Fin n → ℝ) (hy : 0 < pair M y y) :
    (pair M x y)^2 ≤ (pair M y y) * (pair M x x) := by
  let a := pair M y y
  let b := pair M x y
  let w := a • x - b • y
  have hw : 0 ≤ pair M w w := hM.dotProduct_mulVec_nonneg w
  have hxy := pair_sym M hSym x y
  have hyy : pair M y y = a := rfl
  have hxx : pair M x x = pair M x x := rfl
  have hcross : pair M y x = b := hxy.symm
  have hxy' : y ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (M *ᵥ y) := by
    simpa [pair, b] using hcross
  have h_expand : pair M w w =
      a^2 * pair M x x - 2*a*b^2 + a*b^2 := by
    simp only [pair, w, a, b, Matrix.mulVec_sub, Matrix.mulVec_smul,
      dotProduct_sub, dotProduct_smul, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hxy']
    ring
  rw [h_expand] at hw
  dsimp [a,b] at *
  nlinarith [hw,hy]

end
end TiltSchurProjectedCS
