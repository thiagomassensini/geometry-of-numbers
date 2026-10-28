import EulerNewtonMatrix

namespace CarryEulerNewtonAll
open CarrySelfAdjointOperator CarryNativeBinomial Polynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Matrix entries are fixed by the two jet orders, independent of cutoff. -/
theorem euler_newton_matrix_prefix (N M : ℕ) (t : ℝ)
    (i j : Fin N) (p q : Fin M) (hi : (i:ℕ)=(p:ℕ)) (hj : (j:ℕ)=(q:ℕ)) :
    eulerNewtonMatrix N t i j=eulerNewtonMatrix M t p q := by
  unfold eulerNewtonMatrix
  rw [hi, hj]

theorem euler_newton_diagonal (N : ℕ) (t : ℝ) (m : Fin N) :
    eulerNewtonMatrix N t m m=
      (Real.sqrt 2:ℂ)*nativeSourceJetOrderPhase m*Complex.I^(m:ℕ) := by
  simp [eulerNewtonMatrix, shifted_falling_diagonal]

theorem euler_newton_diagonal_ne_zero (N : ℕ) (t : ℝ) (m : Fin N) :
    eulerNewtonMatrix N t m m≠0 := by
  rw [euler_newton_diagonal]
  have hs : (Real.sqrt 2:ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hp : nativeSourceJetOrderPhase m≠0 := by
    intro hz
    have he := native_phase_self_inverse m
    rw [hz, zero_mul] at he
    exact zero_ne_one he
  exact mul_ne_zero (mul_ne_zero hs hp) (pow_ne_zero _ Complex.I_ne_zero)

/-- A true finite coordinate change for every real t, including t=0.
No isometry or physical positivity is inferred from its determinant. -/
theorem euler_newton_det_ne_zero (N : ℕ) (t : ℝ) :
    (eulerNewtonMatrix N t).det≠0 := by
  have ht : (eulerNewtonMatrix N t).BlockTriangular OrderDual.toDual := by
    intro i j h
    have hij : (i:ℕ) < (j:ℕ) := h
    exact euler_newton_above N t i j hij
  rw [Matrix.det_of_lowerTriangular _ ht]
  exact Finset.prod_ne_zero_iff.mpr fun m _ => euler_newton_diagonal_ne_zero N t m

private theorem four_polynomials (m : Fin 4) :
    shiftedFalling m=![1,(X:Polynomial ℂ)-1,X^2-3*X+2,X^3-6*X^2+11*X-6] m := by
  fin_cases m <;>
    norm_num [shiftedFalling, descPochhammer, Polynomial.mul_comp, Polynomial.sub_comp,
      Polynomial.X_comp, Polynomial.one_comp] <;> ring

/-- Exact regression to PR122's full four-source map, for every t and vector. -/
theorem euler_newton_four_regression (t : ℝ) (v : Fin 4 → ℂ) :
    eulerNewton 4 t v=CarryEulerNewton.eulerToNewton t v := by
  funext m
  simp only [eulerNewton, Matrix.mulVec, dotProduct, eulerNewtonMatrix]
  rw [four_polynomials]
  fin_cases m <;>
    norm_num [Fin.sum_univ_succ, CarryEulerNewton.eulerToNewton, nativeSourceJetOrderPhase,
      Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_mul,
      Polynomial.coeff_X_pow] <;> ring_nf <;> norm_num [Complex.I_sq, Polynomial.coeff_one, Polynomial.coeff_X]
  rfl

end
end CarryEulerNewtonAll
