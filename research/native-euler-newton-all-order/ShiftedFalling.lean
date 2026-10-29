import NativeNewtonInput
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace CarryEulerNewtonAll
open CarrySelfAdjointOperator CarryNativeBinomial Polynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The address r becomes Euler's D=r+1. This existing falling-factorial
polynomial is therefore shifted by one, without changing a physical source. -/
def shiftedFalling (m : ℕ) : Polynomial ℂ :=
  (descPochhammer ℂ m).comp (X-1)

theorem shifted_falling_degree (m : ℕ) : (shiftedFalling m).natDegree=m := by
  unfold shiftedFalling
  rw [Polynomial.natDegree_comp, descPochhammer_natDegree]
  have h : (X-(1:Polynomial ℂ)).natDegree=1 := by
    simpa only [Polynomial.C_1] using Polynomial.natDegree_X_sub_C (1:ℂ)
  rw [h, mul_one]

theorem shifted_falling_monic (m : ℕ) : (shiftedFalling m).Monic := by
  simpa [shiftedFalling] using (monic_descPochhammer ℂ m).comp_X_sub_C 1

theorem shifted_falling_diagonal (m : ℕ) : (shiftedFalling m).coeff m=1 := by
  simpa only [shifted_falling_degree] using (shifted_falling_monic m).coeff_natDegree

theorem shifted_falling_above (m j : ℕ) (h : m < j) :
    (shiftedFalling m).coeff j=0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [shifted_falling_degree]; exact h)

theorem shifted_falling_address (m r : ℕ) :
    (shiftedFalling m).eval ((r:ℂ)+1)=(m.factorial:ℂ)*(Nat.choose r m:ℂ) := by
  simp only [shiftedFalling, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one, add_sub_cancel_right]
  rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]

/-- Homogeneous polynomial transport, valid also at t=0. Terms above the
degree vanish before natural subtraction in t^(m-j) can matter. -/
theorem shifted_falling_scaled_eval (N m : ℕ) (hm : m < N) (t z : ℂ) :
    (∑ j : Fin N, (shiftedFalling m).coeff j*t^(m-(j:ℕ))*(t*z)^(j:ℕ))=
      t^m*(shiftedFalling m).eval z := by
  have he := Polynomial.eval_eq_sum_range'
    (p:=shiftedFalling m) (by rw [shifted_falling_degree]; exact hm) z
  rw [he, ← Fin.sum_univ_eq_sum_range (fun j : ℕ => (shiftedFalling m).coeff j*z^j),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (j:ℕ) ≤ m
  · rw [mul_pow]
    have hp : t^(m-(j:ℕ))*t^(j:ℕ)=t^m := by
      rw [← pow_add, Nat.sub_add_cancel hj]
    linear_combination (shiftedFalling m).coeff j*z^(j:ℕ)*hp
  · rw [shifted_falling_above m j (by omega)]
    ring

end
end CarryEulerNewtonAll
