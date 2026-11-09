import SigmaContour51TaylorRemainder
import Mathlib.Tactic

/-!
# Reuse one Taylor coefficient table for a function and its derivative

The Arb contour evaluator forms both the zeta and zeta-derivative Taylor polynomials
from one coefficient list. This module proves that the same construction is sound in
the rational rectangle evaluator: the derivative coefficient at index `k` is exactly
`(k+1)` times the function coefficient at index `k+1`. It supplies the arithmetic
bridge only; it does not certify any coefficient box for zeta.
-/

namespace CarrySigmaObstruction

open ZetaLean

noncomputable section
set_option autoImplicit false

/-- Taylor coefficients of the derivative are shifted and scaled Taylor coefficients
of the original function. -/
theorem contourTaylorCoefficient_deriv_eq_nat_mul
    (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    contourTaylorCoefficient (deriv f) c n =
      ((n + 1 : ℕ) : ℂ) * contourTaylorCoefficient f c (n + 1) := by
  unfold contourTaylorCoefficient
  rw [← iteratedDeriv_succ']
  rw [Nat.factorial_succ]
  push_cast
  have hfact : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hfact]

/-- One rational coefficient table encloses the derivative Taylor polynomial after
shifting by one index and multiplying coefficient `k+1` by `k+1`. -/
theorem contourTaylorDerivativeIntervalPolynomial_from_function_coefficients_contains
    {f : ℂ → ℂ} {c z : ℂ} {coeff : ℕ → ComplexInterval}
    {deltaBox : ComplexInterval} {delta : ℂ} {N : ℕ}
    (hcoeff : ∀ k ≤ N, (coeff k).contains (contourTaylorCoefficient f c k))
    (hdelta : deltaBox.contains delta)
    (hdeltaExact : delta = z - c) :
    (contourTaylorIntervalPolynomial
      (fun k => ComplexInterval.smulQ ((k + 1 : ℕ) : ℚ) (coeff (k + 1)))
      deltaBox N).contains (contourTaylorDerivativePolynomial f c z N) := by
  have hpoly := contourTaylorIntervalPolynomial_contains
    (coeff := fun k => ComplexInterval.smulQ ((k + 1 : ℕ) : ℚ) (coeff (k + 1)))
    (coeffExact := fun k => contourTaylorCoefficient (deriv f) c k)
    (deltaBox := deltaBox) (delta := delta) hdelta N ?_
  · simpa [contourTaylorDerivativePolynomial, hdeltaExact,
      contourTaylorCoefficient_deriv_eq_nat_mul] using hpoly
  · intro k hk
    have hscale := ComplexInterval.contains_smulQ
      (q := ((k + 1 : ℕ) : ℚ)) (hcoeff (k + 1) (by omega))
    simpa [contourTaylorCoefficient_deriv_eq_nat_mul] using hscale

/-- Inflating the derivative polynomial from the shared function-coefficient table by
a valid derivative Taylor remainder encloses the exact derivative value. -/
theorem contourTaylorDerivativeIntervalPolynomial_from_function_coefficients_inflate_contains
    {f : ℂ → ℂ} {c z : ℂ} {coeff : ℕ → ComplexInterval}
    {deltaBox : ComplexInterval} {delta : ℂ} {err : ℚ} {N : ℕ}
    (hcoeff : ∀ k ≤ N, (coeff k).contains (contourTaylorCoefficient f c k))
    (hdelta : deltaBox.contains delta)
    (hdeltaExact : delta = z - c)
    (hrem : ‖deriv f z - contourTaylorDerivativePolynomial f c z N‖ ≤ (err : ℝ)) :
    (contourTaylorIntervalPolynomial
      (fun k => ComplexInterval.smulQ ((k + 1 : ℕ) : ℚ) (coeff (k + 1)))
      deltaBox N).inflate err |>.contains (deriv f z) := by
  have hpoly := contourTaylorDerivativeIntervalPolynomial_from_function_coefficients_contains
    hcoeff hdelta hdeltaExact
  exact ComplexInterval.contains_inflate hpoly hrem

/-- A single Taylor/Cauchy certificate produces simultaneous rational boxes for a function
and its derivative. The analytic hypotheses and both rational tail comparisons are explicit;
the coefficient boxes and displacement box are shared. -/
theorem contourTaylorCauchyValueAndDerivativeBoxes
    {f : ℂ → ℂ} {c z : ℂ} {r M q : ℝ} {N : ℕ}
    {coeff : ℕ → ComplexInterval} {deltaBox : ComplexInterval}
    {valueError derivativeError : ℚ}
    (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (Metric.ball c r))
    (hdf : DifferentiableOn ℂ (deriv f) (Metric.ball c r))
    (hM : ∀ w ∈ Metric.sphere c r, ‖f w‖ ≤ M)
    (hz : z ∈ Metric.ball c r)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdeltaNorm : ‖z - c‖ ≤ q * r)
    (hcoeff : ∀ k ≤ N,
      (coeff k).contains (contourTaylorCoefficient f c k))
    (hdelta : deltaBox.contains (z - c))
    (hvalueTail : M * q ^ (N + 1) / (1 - q) ≤ (valueError : ℝ))
    (hderivativeTail : (M / r) * q ^ N *
      (((N + 1 : ℕ) : ℝ) - (N : ℝ) * q) / (1 - q) ^ 2 ≤
        (derivativeError : ℝ)) :
    ((contourTaylorIntervalPolynomial coeff deltaBox (N + 1)).inflate valueError).contains
        (f z) ∧
      ((contourTaylorIntervalPolynomial
        (fun k => ComplexInterval.smulQ ((k + 1 : ℕ) : ℚ) (coeff (k + 1)))
        deltaBox N).inflate derivativeError).contains (deriv f z) := by
  have hvalueCauchy := contourTaylorRemainder_norm_le (N := N)
    hr hf hM hz hq0 hq1 hdeltaNorm
  have hvalueRemainder := hvalueCauchy.trans hvalueTail
  have hvalueCoeff : ∀ k < N + 1,
      (coeff k).contains (contourTaylorCoefficient f c k) := by
    intro k hk
    exact hcoeff k (by omega)
  have hvalue := contourTaylorIntervalPolynomial_inflate_contains
    hvalueCoeff hdelta hvalueRemainder
  have hderivativeCauchy := contourTaylorDerivativeRemainder_norm_le (N := N)
    hr hf hdf hM hz hq0 hq1 hdeltaNorm
  have hderivativeRemainder := hderivativeCauchy.trans hderivativeTail
  have hderivative :=
    contourTaylorDerivativeIntervalPolynomial_from_function_coefficients_inflate_contains
      hcoeff hdelta rfl hderivativeRemainder
  exact ⟨hvalue, hderivative⟩

#print axioms contourTaylorCoefficient_deriv_eq_nat_mul
#print axioms contourTaylorDerivativeIntervalPolynomial_from_function_coefficients_contains
#print axioms contourTaylorDerivativeIntervalPolynomial_from_function_coefficients_inflate_contains
#print axioms contourTaylorCauchyValueAndDerivativeBoxes

end
end CarrySigmaObstruction
