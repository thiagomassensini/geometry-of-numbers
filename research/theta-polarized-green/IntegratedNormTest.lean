import ThetaCrossObstruction
import ProductResidual

/-! Test the concrete candidate e_n ↦ P_n IN THE ORIGINAL theta product
integral. The failure is integrated, not merely pointwise. All bounds below
come from existing theta-source estimates, not from a Hankel sign consumer. -/
namespace CarryThetaPolarized
open CarrySelfAdjointOperator Polynomial
noncomputable section
set_option autoImplicit false

theorem theta_first_polynomial_square_integral :
    nativeXiPolynomialIntegral (nativeThetaMomentPolynomial 0 ^ 2) =
      completedNativeXiCosineMoment 2 /
        (4 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 2) := by
  have hp : nativeThetaMomentPolynomial 0 ^ 2 =
      Polynomial.monomial 4
        (1 / (4 * completedNativeRealEvenCharacteristicCoefficient 0 ^ 2)) := by
    apply Polynomial.funext
    intro u
    simp only [Polynomial.eval_pow, Polynomial.eval_monomial, moment_zero_eval]
    ring
  rw [hp, show 4 = 2*2 by omega, nativeXiPolynomialIntegral_monomial_even]
  ring

/-- A source inequality for this diagnostic, with no Hankel PosDef premise. -/
theorem xi_fourth_moment_lt_twice_mass_second :
    completedNativeXiCosineMoment 2 <
      2 * completedNativeRealEvenCharacteristicCoefficient 0 * completedNativeXiCosineMoment 1 := by
  have hfirst : (1/50 : ℝ) < completedNativeXiCosineMoment 1 := by
    rw [completedNativeXiCosineMoment_one_eq_thetaTailMoments]
    linarith [completedNativeThetaTailMoment_zero_gt, completedNativeThetaTailMoment_two_lt]
  have hsecond : completedNativeXiCosineMoment 2 < (1/250 : ℝ) := by
    rw [completedNativeXiCosineMoment_two_eq_thetaTailMoments]
    linarith [completedNativeThetaTailMoment_two_lt, completedNativeThetaTailMoment_nonneg 4]
  have hc := completedNativeRealEvenCharacteristicCoefficient_zero_ge_third
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (le_of_lt (lt_trans (by norm_num) hfirst))]

/-- The naive identification of the zeroth native jet with P_0 in L2(Phi)
already has the wrong norm. No rescaling of the original data is performed. -/
theorem theta_first_polynomial_square_integral_lt_native :
    nativeXiPolynomialIntegral (nativeThetaMomentPolynomial 0 ^ 2) <
      canonicalCompletedNativeLogDerivativeMoment 0 := by
  have hc : 0 < completedNativeRealEvenCharacteristicCoefficient 0 := by
    linarith [completedNativeRealEvenCharacteristicCoefficient_zero_ge_third]
  have hzero : canonicalCompletedNativeLogDerivativeMoment 0 =
      completedNativeXiCosineMoment 1 /
        (2 * completedNativeRealEvenCharacteristicCoefficient 0) := by
    rw [canonicalCompletedNativeLogDerivativeMoment_eq,
      completedNativeRealEvenCharacteristicCoefficient_one_eq_xiCosineMoment]
    norm_num
    ring
  rw [theta_first_polynomial_square_integral, hzero]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have hm := mul_lt_mul_of_pos_right xi_fourth_moment_lt_twice_mass_second
    (mul_pos (by norm_num : (0 : ℝ) < 2) hc)
  nlinarith only [hm]

/-- Consequently the exact product residual is NOT zero even after
integration, for the zeroth/zeroth pairing of this particular candidate. -/
theorem theta_product_residual_zero_zero_integral_pos :
    0 < nativeXiPolynomialIntegral (thetaProductResidual 0 0) := by
  simp only [thetaProductResidual, zero_add, map_sub]
  rw [nativeThetaMomentPolynomial_integral]
  have h := theta_first_polynomial_square_integral_lt_native
  rw [pow_two] at h
  exact sub_pos.mpr h

end
end CarryThetaPolarized
