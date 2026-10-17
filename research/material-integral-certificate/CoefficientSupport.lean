import CoefficientData

namespace CarryIntegralCertificate
open Polynomial
set_option autoImplicit false

theorem thetaPolynomialCode_coeff_zero (n j : ℕ) (hj : n < j) :
    (thetaPolynomialCode n).coeff j = 0 := by
  unfold thetaPolynomialCode
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro r hr
  have hr' := Finset.mem_range.mp hr
  rw [coeff_C_mul_X_pow,if_neg (by omega)]

end CarryIntegralCertificate
