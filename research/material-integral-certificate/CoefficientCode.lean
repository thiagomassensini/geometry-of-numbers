import CoefficientStep0
import CoefficientStep1
import CoefficientStep2
import CoefficientStep3

namespace CarryIntegralCertificate
open Polynomial
set_option autoImplicit false

theorem thetaPolynomialCode_correct (n : ℕ) (hn : n ≤ 16) :
    thetaDerivativePolynomial n = thetaPolynomialCode n := by
  induction n with
  | zero => norm_num [thetaDerivativePolynomial,thetaPolynomialCode,thetaCoefficientCode]
  | succ n ih =>
    rw [thetaDerivativePolynomial,ih (by omega)]
    by_cases h0 : n ≤ 3
    · exact thetaPolynomialCode_step0 n (by omega) h0
    by_cases h1 : n ≤ 7
    · exact thetaPolynomialCode_step1 n (by omega) h1
    by_cases h2 : n ≤ 11
    · exact thetaPolynomialCode_step2 n (by omega) h2
    · exact thetaPolynomialCode_step3 n (by omega) (by omega)

end CarryIntegralCertificate
