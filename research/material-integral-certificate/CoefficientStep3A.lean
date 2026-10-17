import CoefficientSupport

namespace CarryIntegralCertificate
open Polynomial
set_option autoImplicit false
set_option maxHeartbeats 4000000

set_option linter.unusedSimpArgs false in
theorem thetaPolynomialCode_step3a (n : ℕ) (hlo : 12 ≤ n) (hhi : n ≤ 13) :
    (C (1/2)-C 2*X)*thetaPolynomialCode n +
      C 2*X*(thetaPolynomialCode n).derivative = thetaPolynomialCode (n+1) := by
  have hl := hlo
  have hu := hhi
  rw [show (C (1/2)-C 2*X)*thetaPolynomialCode n +
    C 2*X*(thetaPolynomialCode n).derivative =
    C (1/2)*thetaPolynomialCode n-C 2*(X*thetaPolynomialCode n)+
      C 2*(X*(thetaPolynomialCode n).derivative) by ring]
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ n+1
  · interval_cases n <;> interval_cases j <;>
      norm_num [thetaPolynomialCode,thetaCoefficientCode,Finset.sum_range_succ,
        coeff_add,coeff_sub,coeff_C_mul,coeff_X_mul,coeff_X_mul_zero,coeff_derivative]
  · cases j with
    | zero => omega
    | succ j =>
      simp (disch := omega) [coeff_add,coeff_sub,coeff_C_mul,
        coeff_X_mul,coeff_derivative,thetaPolynomialCode_coeff_zero]

end CarryIntegralCertificate
