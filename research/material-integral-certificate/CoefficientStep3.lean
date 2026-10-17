import CoefficientStep3A
import CoefficientStep3B
namespace CarryIntegralCertificate
open Polynomial
set_option autoImplicit false

theorem thetaPolynomialCode_step3 (n : ℕ) (hlo : 12 ≤ n) (hhi : n ≤ 15) :
    (C (1/2)-C 2*X)*thetaPolynomialCode n +
      C 2*X*(thetaPolynomialCode n).derivative = thetaPolynomialCode (n+1) := by
  by_cases hn : n ≤ 13
  · exact thetaPolynomialCode_step3a n hlo hn
  · exact thetaPolynomialCode_step3b n (by omega) hhi

end CarryIntegralCertificate
