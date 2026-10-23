import CarrySelfAdjointOperator.NativeSourceThetaGreenTransport
import Mathlib.Tactic

/-! Polarized tests of the EXISTING theta Green transport.
These are identities on the downstream polynomial readout, not a definition
of a new physical carrier or an isometry of the original completed state. -/
namespace CarryThetaPolarized
open CarrySelfAdjointOperator Polynomial MeasureTheory Set Filter XiThetaCosine
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- The fixed Green operator has an explicit product defect. In particular it
is neither a derivation nor a multiplicative, norm-preserving transport. -/
theorem green_product_defect (P Q : ℝ[X]) :
    nativeThetaGreenPolynomial (P * Q) -
      P * nativeThetaGreenPolynomial Q - Q * nativeThetaGreenPolynomial P =
        2 * P.derivative * Q.derivative + (1/4 : ℝ) • (P * Q) := by
  simp only [nativeThetaGreenPolynomial, Polynomial.derivative_mul,
    Polynomial.derivative_add, smul_eq_C_mul]
  ring

/-- Both original fluxes and their common tail correction are retained. -/
theorem green_flux_product (P Q : ℝ[X]) (u : ℝ) :
    nativeThetaGreenFlux (P * Q) u =
      P.eval u * nativeThetaGreenFlux Q u +
        Q.eval u * nativeThetaGreenFlux P u -
          P.eval u * Q.eval u * thetaTailFirst u := by
  simp only [nativeThetaGreenFlux, Polynomial.derivative_mul,
    Polynomial.eval_mul, Polynomial.eval_add]
  ring

/-- Full product transport, including derivative crosses and BOTH center
traces. No condition at the center or vanishing boundary is assumed. -/
theorem green_product_integral (P Q : ℝ[X]) :
    nativeXiPolynomialIntegral (P * Q) =
      (∫ u in Ioi (0 : ℝ),
        (P.derivative.derivative.eval u * Q.eval u +
          2 * P.derivative.eval u * Q.derivative.eval u +
          P.eval u * Q.derivative.derivative.eval u -
          (1/4 : ℝ) * P.eval u * Q.eval u) * thetaTail u) +
      P.eval 0 * Q.eval 0 / 2 +
        (P.derivative.eval 0 * Q.eval 0 +
          P.eval 0 * Q.derivative.eval 0) * thetaTail 0 := by
  rw [nativeXiPolynomialIntegral_eq_thetaGreen_integral]
  simp only [nativeThetaGreenPolynomial, Polynomial.derivative_mul,
    Polynomial.derivative_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with u
  ring

/-- Two independent finite inputs, with the original source polynomials. -/
def thetaBilinearPolynomial (s N M : ℕ) (x : Fin N → ℝ) (y : Fin M → ℝ) : ℝ[X] :=
  ∑ i : Fin N, ∑ j : Fin M,
    (x i * y j) • nativeThetaMomentPolynomial (i.val + j.val + s)

theorem thetaBilinearPolynomial_integral (s N M : ℕ)
    (x : Fin N → ℝ) (y : Fin M → ℝ) :
    nativeXiPolynomialIntegral (thetaBilinearPolynomial s N M x y) =
      ∑ i : Fin N, ∑ j : Fin M,
        x i * y j * canonicalCompletedNativeLogDerivativeMoment (i.val + j.val + s) := by
  simp only [thetaBilinearPolynomial, map_sum, map_smul,
    nativeThetaMomentPolynomial_integral, smul_eq_mul]

theorem thetaBilinearPolynomial_center_traces (s N M : ℕ)
    (x : Fin N → ℝ) (y : Fin M → ℝ) :
    (thetaBilinearPolynomial s N M x y).eval 0 = 0 ∧
      (thetaBilinearPolynomial s N M x y).derivative.eval 0 = 0 := by
  have hc (d : ℕ) (hd : d < 2) :
      (thetaBilinearPolynomial s N M x y).coeff d = 0 := by
    simp only [thetaBilinearPolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_smul, smul_eq_mul,
      nativeThetaMomentPolynomial_coeff_below_two _ _ hd, mul_zero,
      Finset.sum_const_zero]
  constructor
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using hc 0 (by omega)
  · rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simpa using hc 1 (by omega)

/-- The entire bilinear moment readout survives the original Green transfer.
This preserves all crosses, but does not identify a Hilbert-state transport. -/
theorem native_bilinear_eq_green_integral (s N M : ℕ)
    (x : Fin N → ℝ) (y : Fin M → ℝ) :
    (∑ i : Fin N, ∑ j : Fin M,
      x i * y j * canonicalCompletedNativeLogDerivativeMoment (i.val + j.val + s)) =
      ∫ u in Ioi (0 : ℝ),
        (nativeThetaGreenPolynomial (thetaBilinearPolynomial s N M x y)).eval u *
          thetaTail u := by
  rw [← thetaBilinearPolynomial_integral, nativeXiPolynomialIntegral_eq_thetaGreen_integral]
  obtain ⟨hv, hd⟩ := thetaBilinearPolynomial_center_traces s N M x y
  simp only [hv, hd, zero_div, zero_mul, add_zero]

end
end CarryThetaPolarized
