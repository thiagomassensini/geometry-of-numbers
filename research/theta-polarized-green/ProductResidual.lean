import PolynomialInformation

/-! The exact residual of the PARTICULAR candidate sending test monomials
to the original source polynomials P_n. No new metric, source, or positivity
condition is inserted. This is a diagnostic, not a physical-state transport. -/
namespace CarryThetaPolarized
open CarrySelfAdjointOperator Polynomial MeasureTheory Set XiThetaCosine
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem momentPolynomial_center_traces (n : ℕ) :
    (nativeThetaMomentPolynomial n).eval 0 = 0 ∧
      (nativeThetaMomentPolynomial n).derivative.eval 0 = 0 := by
  constructor
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using
      nativeThetaMomentPolynomial_coeff_below_two n 0 (by omega)
  · rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simpa using nativeThetaMomentPolynomial_coeff_below_two n 1 (by omega)

/-- Failure of multiplication in the ORIGINAL polynomial transform. -/
def thetaProductResidual (i j : ℕ) : ℝ[X] :=
  nativeThetaMomentPolynomial (i+j) -
    nativeThetaMomentPolynomial i * nativeThetaMomentPolynomial j

theorem thetaProductResidual_center_traces (i j : ℕ) :
    (thetaProductResidual i j).eval 0 = 0 ∧
      (thetaProductResidual i j).derivative.eval 0 = 0 := by
  obtain ⟨hi, hdi⟩ := momentPolynomial_center_traces i
  obtain ⟨hj, hdj⟩ := momentPolynomial_center_traces j
  obtain ⟨hs, hds⟩ := momentPolynomial_center_traces (i+j)
  simp only [thetaProductResidual, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.eval_add,
    hi, hj, hs, hdi, hdj, hds, mul_zero, add_zero, sub_zero, and_self]

/-- The same bulk defect, with EVERY derivative cross term exposed. -/
theorem thetaProductResidual_green_formula (i j : ℕ) :
    nativeThetaGreenPolynomial (thetaProductResidual i j) =
      nativeThetaGreenPolynomial (nativeThetaMomentPolynomial (i+j)) -
        nativeThetaMomentPolynomial i * nativeThetaGreenPolynomial (nativeThetaMomentPolynomial j) -
        nativeThetaMomentPolynomial j * nativeThetaGreenPolynomial (nativeThetaMomentPolynomial i) -
        2 * (nativeThetaMomentPolynomial i).derivative * (nativeThetaMomentPolynomial j).derivative -
        (1/4 : ℝ) • (nativeThetaMomentPolynomial i * nativeThetaMomentPolynomial j) := by
  have h := green_product_defect (nativeThetaMomentPolynomial i) (nativeThetaMomentPolynomial j)
  simp only [thetaProductResidual, nativeThetaGreenPolynomial,
    Polynomial.derivative_sub, smul_sub] at *
  linear_combination -h

/-- An exact all-order bilinear identity WITH residual. The positive product
integral alone is not the native Hankel kernel. The residual is not discarded. -/
theorem canonical_pairing_eq_theta_product_add_green_residual (i j : ℕ) :
    canonicalCompletedNativeLogDerivativeMoment (i+j) =
      nativeXiPolynomialIntegral (nativeThetaMomentPolynomial i * nativeThetaMomentPolynomial j) +
        ∫ u in Ioi (0 : ℝ),
          (nativeThetaGreenPolynomial (thetaProductResidual i j)).eval u * thetaTail u := by
  have h := nativeXiPolynomialIntegral_eq_thetaGreen_integral (thetaProductResidual i j)
  obtain ⟨hv, hd⟩ := thetaProductResidual_center_traces i j
  rw [hv, hd] at h
  simp only [zero_div, zero_mul, add_zero] at h
  rw [thetaProductResidual, map_sub, nativeThetaMomentPolynomial_integral] at h
  dsimp only [thetaProductResidual]
  linarith

/-- Positivity of the genuine theta product integral is independent of the
sign of the retained native residual. It cannot absorb that residual for free. -/
theorem theta_polynomial_square_integral_nonneg (P : ℝ[X]) :
    0 ≤ nativeXiPolynomialIntegral (P^2) := by
  change 0 ≤ ∫ u in Ioi (0 : ℝ), (P^2).eval u * completedNativeXiCosineKernel u
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Polynomial.eval_pow]
  exact mul_nonneg (sq_nonneg _) (completedNativeXiCosineKernel_pos hu.le).le

/-- The apparent missing boundary is accounted for by zero center traces
and the already-proved decay at infinity, not by a normalization. -/
theorem thetaProductResidual_flux_zero_at_center (i j : ℕ) :
    nativeThetaGreenFlux (thetaProductResidual i j) 0 = 0 := by
  obtain ⟨hv, hd⟩ := thetaProductResidual_center_traces i j
  simp only [nativeThetaGreenFlux, hv, hd, zero_mul, sub_self]

end
end CarryThetaPolarized
