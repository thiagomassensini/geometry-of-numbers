import SourceCoordinates
import CarrySelfAdjointOperator.CompletedNativeChiralReturnBoundaryCoefficientProvenance

/-! Taylor extraction of the SAME completed transverse source at arbitrary
order. The coefficients are read after complete synthesis; no sign is used. -/
namespace CarrySourceLaw
open CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

def transverseSource (t : ℂ) : ℂ :=
  -Complex.I * completedNativeOperatorLogDerivative (Complex.I*t)

def transverseCoefficient (n : ℕ) : ℂ :=
  -Complex.I * Complex.I^n * 2 * completedNativeGreenResponseTaylorCoefficient n

theorem transverseSource_analytic : AnalyticAt ℂ transverseSource 0 := by
  have h := nativeSourceLogSlope_analyticAt.fun_comp_of_eq
    (show AnalyticAt ℂ (fun t : ℂ => Complex.I*t) 0 by fun_prop) (by simp)
  exact analyticAt_const.mul h

theorem transverseCoefficient_eq_derivative (n : ℕ) :
    iteratedDeriv n transverseSource 0 / (n.factorial : ℂ) =
      transverseCoefficient n := by
  unfold transverseSource transverseCoefficient completedNativeGreenResponseTaylorCoefficient
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_mul_zero,
    completedNativeOperatorLogDerivative_eq_twice_greenResponse,
    iteratedDeriv_const_mul_field]
  ring

theorem transverseCoefficient_even (j : ℕ) : transverseCoefficient (2*j) = 0 := by
  simp [transverseCoefficient, completedNativeGreenResponseTaylorCoefficient_even_eq_zero]

theorem transverseCoefficient_odd (j : ℕ) :
    transverseCoefficient (2*j+1) =
      (-1 : ℂ)^j * (2 * canonicalCompletedNativeLogDerivativeMoment j : ℝ) := by
  rw [transverseCoefficient, completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical]
  rw [pow_add, show Complex.I^(2*j) = (-1:ℂ)^j by rw [pow_mul, Complex.I_sq]]
  push_cast
  ring_nf
  norm_num [Complex.I_sq]

/-- One original analytic source, every finite Taylor order, full remainder.
No moment positivity, inverse prefix, spectral datum or fitted coefficient. -/
theorem source_exact_remainder (order : ℕ) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ t : ℂ in nhds 0,
      transverseSource t = (∑ n ∈ Finset.range order,
        transverseCoefficient n * t^n) + t^order * R t := by
  obtain ⟨R,hR,he⟩ := transverseSource_analytic.exists_eventuallyEq_sum_add_pow_mul order
  refine ⟨R,hR,?_⟩
  filter_upwards [he] with t ht
  rw [ht]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [← transverseCoefficient_eq_derivative]
  simp only [smul_eq_mul]
  ring

end
end CarrySourceLaw
