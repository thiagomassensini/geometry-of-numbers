import NullExtension

namespace CarryNegativeDirection
open CarrySelfAdjointOperator
open scoped BigOperators Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Completing the square needs a solution Ay=b, not an inverse of A. -/
theorem source_sewing_of_solution (m : ℕ → ℝ) (s n : ℕ) (y : Fin n → ℝ)
    (hy : sourceMomentMatrix m s n *ᵥ y=sourceMomentCoupling m s n)
    (x : Fin n → ℝ) (t : ℝ) :
    sourceMomentQuadratic m s (n+1) (Fin.snoc x t)=
      sourceMomentQuadratic m s n (x+t • y)+
      (m (2*n+s)-sourceMomentCoupling m s n ⬝ᵥ y)*t^2 := by
  have ht : (sourceMomentMatrix m s n)ᵀ=sourceMomentMatrix m s n := by
    ext i j
    simp [sourceMomentMatrix,add_comm]
  have hc : y ⬝ᵥ (sourceMomentMatrix m s n *ᵥ x)=sourceMomentCoupling m s n ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec,← ht,Matrix.vecMul_transpose,hy]
  have hq : sourceMomentQuadratic m s n (x+t • y)=
      sourceMomentQuadratic m s n x+2*t*(sourceMomentCoupling m s n ⬝ᵥ x)+
      (sourceMomentCoupling m s n ⬝ᵥ y)*t^2 := by
    simp only [sourceMomentQuadratic,star_trivial,Matrix.mulVec_add,Matrix.mulVec_smul,hy,
      add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,hc]
    rw [dotProduct_comm x (sourceMomentCoupling m s n),dotProduct_comm y (sourceMomentCoupling m s n)]
    ring
  rw [sourceMomentQuadratic_snoc,hq]
  ring

theorem solution_witness_energy (m : ℕ → ℝ) (s n : ℕ) (y : Fin n → ℝ)
    (hy : sourceMomentMatrix m s n *ᵥ y=sourceMomentCoupling m s n) :
    sourceMomentQuadratic m s (n+1) (Fin.snoc (-y) 1)=
      m (2*n+s)-sourceMomentCoupling m s n ⬝ᵥ y := by
  rw [source_sewing_of_solution m s n y hy]
  simp [sourceMomentQuadratic]

/-- A singular system may have many solutions, but their scalar residual is identical. -/
theorem solution_residual_independent (m : ℕ → ℝ) (s n : ℕ) (y z : Fin n → ℝ)
    (hy : sourceMomentMatrix m s n *ᵥ y = sourceMomentCoupling m s n)
    (hz : sourceMomentMatrix m s n *ᵥ z = sourceMomentCoupling m s n) :
    m (2*n+s)-sourceMomentCoupling m s n ⬝ᵥ y =
      m (2*n+s)-sourceMomentCoupling m s n ⬝ᵥ z := by
  have ht : (sourceMomentMatrix m s n)ᵀ = sourceMomentMatrix m s n := by
    ext i j
    simp [sourceMomentMatrix,add_comm]
  have hc : z ⬝ᵥ (sourceMomentMatrix m s n *ᵥ y) = sourceMomentCoupling m s n ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec,← ht,Matrix.vecMul_transpose,hz]
  rw [hy,dotProduct_comm z (sourceMomentCoupling m s n)] at hc
  rw [hc]

/-- For a compatible singular prefix, PSD reduces to this residual, with no inverse. -/
theorem psd_extension_iff_solution_residual (m : ℕ → ℝ) (s n : ℕ)
    (hA : (sourceMomentMatrix m s n).PosSemidef) (y : Fin n → ℝ)
    (hy : sourceMomentMatrix m s n *ᵥ y=sourceMomentCoupling m s n) :
    (sourceMomentMatrix m s (n+1)).PosSemidef ↔
      0 ≤ m (2*n+s)-sourceMomentCoupling m s n ⬝ᵥ y := by
  constructor
  · intro hp
    have ht := hp.dotProduct_mulVec_nonneg (Fin.snoc (-y) 1)
    change 0 ≤ sourceMomentQuadratic m s (n+1) (Fin.snoc (-y) 1) at ht
    rwa [solution_witness_energy m s n y hy] at ht
  · intro hr
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (sourceMomentMatrix_isHermitian m s (n+1))
    intro z
    change 0 ≤ sourceMomentQuadratic m s (n+1) z
    have he : Fin.snoc (Fin.init z) (z (Fin.last n))=z := Fin.snoc_init_self z
    rw [← he,source_sewing_of_solution m s n y hy]
    exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (mul_nonneg hr (sq_nonneg _))

end
end CarryNegativeDirection
