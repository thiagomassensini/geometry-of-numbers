import PolarizedGreen

/-! Exact information tests BEFORE the scalar integral. These are maps on
finite TEST COEFFICIENTS, not on the full material Carry state. -/
namespace CarryThetaPolarized
open CarrySelfAdjointOperator Polynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def thetaInputPolynomial (N : ℕ) (x : Fin N → ℝ) : ℝ[X] :=
  ∑ i : Fin N, x i • nativeThetaMomentPolynomial i.val

theorem thetaInputPolynomial_succ (N : ℕ) (x : Fin (N+1) → ℝ) :
    thetaInputPolynomial (N+1) x =
      thetaInputPolynomial N (fun i => x i.castSucc) +
        x (Fin.last N) • nativeThetaMomentPolynomial N := by
  simp only [thetaInputPolynomial, Fin.sum_univ_castSucc, Fin.val_castSucc,
    Fin.val_last]

theorem moment_top_coefficient_ne_zero (n : ℕ) :
    (nativeThetaMomentPolynomial n).coeff (2*n+2) ≠ 0 := by
  rw [nativeThetaMomentPolynomial_coeff_top]
  apply mul_ne_zero (inv_ne_zero completedNativeRealEvenCharacteristicCoefficient_zero_ne_zero)
  unfold nativeThetaMomentTopCoefficient
  apply div_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  · positivity

theorem thetaInputPolynomial_coeff_last (N : ℕ) (x : Fin (N+1) → ℝ) :
    (thetaInputPolynomial (N+1) x).coeff (2*N+2) =
      x (Fin.last N) * (nativeThetaMomentPolynomial N).coeff (2*N+2) := by
  rw [thetaInputPolynomial_succ]
  simp only [Polynomial.coeff_add, thetaInputPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, smul_eq_mul]
  have hs : (∑ i : Fin N, x i.castSucc *
      (nativeThetaMomentPolynomial i.val).coeff (2*N+2)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [nativeThetaMomentPolynomial_coeff_above _ _ (by have := i.isLt; omega), mul_zero]
  rw [hs, zero_add]

theorem thetaInputPolynomial_zero_iff (N : ℕ) (x : Fin N → ℝ) :
    thetaInputPolynomial N x = 0 ↔ x = 0 := by
  constructor
  · induction N with
    | zero => intro _; funext i; exact Fin.elim0 i
    | succ N ih =>
      intro hz
      have ht := congrArg (fun P : ℝ[X] => P.coeff (2*N+2)) hz
      rw [thetaInputPolynomial_coeff_last, Polynomial.coeff_zero] at ht
      have hx : x (Fin.last N) = 0 :=
        (mul_eq_zero.mp ht).resolve_right (moment_top_coefficient_ne_zero N)
      have hp : thetaInputPolynomial N (fun i => x i.castSucc) = 0 := by
        rw [thetaInputPolynomial_succ, hx, zero_smul, add_zero] at hz
        exact hz
      have hi := ih (fun i => x i.castSucc) hp
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hx
      · exact congrFun hi j
  · intro hx
    simp [hx, thetaInputPolynomial]

theorem thetaInputPolynomial_injective (N : ℕ) :
    Function.Injective (thetaInputPolynomial N) := by
  intro x y hxy
  have hz : thetaInputPolynomial N (x-y) = 0 := by
    simp only [thetaInputPolynomial, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp ((thetaInputPolynomial_zero_iff N (x-y)).mp hz)

/-- The differential Green transfer itself does not erase polynomial data. -/
theorem greenPolynomial_zero_iff (P : ℝ[X]) :
    nativeThetaGreenPolynomial P = 0 ↔ P = 0 := by
  constructor
  · intro h
    have ht := congrArg (fun Q : ℝ[X] => Q.coeff P.natDegree) h
    have hd : P.coeff (P.natDegree+1+1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [nativeThetaGreenPolynomial, Polynomial.coeff_sub,
      Polynomial.coeff_derivative, Polynomial.coeff_smul, smul_eq_mul,
      Polynomial.coeff_zero, hd, zero_mul, zero_sub] at ht
    have hc : P.coeff P.natDegree = 0 := by linarith
    exact Polynomial.leadingCoeff_eq_zero.mp (by simpa only [Polynomial.coeff_natDegree] using hc)
  · intro h
    simp [h, nativeThetaGreenPolynomial]

theorem greenPolynomial_injective : Function.Injective nativeThetaGreenPolynomial := by
  intro P Q h
  have hz : nativeThetaGreenPolynomial (P-Q) = 0 := by
    simp only [nativeThetaGreenPolynomial, Polynomial.derivative_sub, smul_sub] at *
    linear_combination h
  exact sub_eq_zero.mp ((greenPolynomial_zero_iff (P-Q)).mp hz)

theorem thetaGreenInput_injective (N : ℕ) :
    Function.Injective (fun x : Fin N → ℝ =>
      nativeThetaGreenPolynomial (thetaInputPolynomial N x)) :=
  greenPolynomial_injective.comp (thetaInputPolynomial_injective N)

end
end CarryThetaPolarized
