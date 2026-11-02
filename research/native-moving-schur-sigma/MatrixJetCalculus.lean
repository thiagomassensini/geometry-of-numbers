import Mathlib

/-! Finite expansion of the existing Euclidean operator. No metric is changed. -/
namespace CarryMovingSigma
open Matrix
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem euclideanCLM_basis_expansion {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    toEuclideanCLM (𝕜 := ℝ) M =
      ∑ i : Fin N, ∑ j : Fin N,
        M i j • toEuclideanCLM (𝕜 := ℝ) (Matrix.single i j (1:ℝ)) := by
  calc
    _ = toEuclideanCLM (𝕜 := ℝ) (∑ i : Fin N, ∑ j : Fin N, Matrix.single i j (M i j)) :=
      congrArg (toEuclideanCLM (𝕜 := ℝ)) (matrix_eq_sum_single M)
    _ = _ := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have he : Matrix.single i j (M i j) = M i j • Matrix.single i j (1:ℝ) := by
        rw [Matrix.smul_single]
        simp
      rw [he,map_smul]

/-- Entrywise derivatives transported to the original operator norm by a finite
basis expansion, avoiding any identification of distinct matrix norm instances. -/
theorem euclideanCLM_hasDerivAt_of_entries {N : ℕ}
    (G : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (D : Matrix (Fin N) (Fin N) ℝ) (t : ℝ)
    (h : ∀ i j, HasDerivAt (fun x => G x i j) (D i j) t) :
    HasDerivAt (fun x => toEuclideanCLM (𝕜 := ℝ) (G x))
      (toEuclideanCLM (𝕜 := ℝ) D) t := by
  have hs := HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    HasDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) =>
      (h i j).smul_const (toEuclideanCLM (𝕜 := ℝ) (Matrix.single i j (1:ℝ)))))
  simpa only [← euclideanCLM_basis_expansion] using hs

end
end CarryMovingSigma
