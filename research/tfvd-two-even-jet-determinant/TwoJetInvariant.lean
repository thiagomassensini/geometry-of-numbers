import SourceApplication

/-! The two-even-jet determinant is extracted from the SAME completed source.
No positivity of moments, prefixes or individual terms is assumed. -/
namespace CarryTwoEvenJets
open CarrySelfAdjointOperator PhysicalSewing CPFormal.Analytic.Cp
open Filter Topology
open scoped BigOperators ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Four independent source-jet slots. Their diagonal is quartic, not a norm. -/
def polarizedQuartic (a b c d : Fin 4 → ℂ) : ℂ :=
  a 0*b 1*c 1*d 2 + 3*a 0*b 0*c 1*d 3 - 4*a 0*b 0*c 2*d 2

def quartic (v : Fin 4 → ℂ) : ℂ := polarizedQuartic v v v v

/-- Actual even Taylor coefficients of the original completed characteristic. -/
def nativeEvenJets : Fin 4 → ℂ := fun j => completedNativeEvenCharacteristicCoefficient j

/-- These are readouts of the canonical source, not independently assigned coefficients. -/
theorem native_three_convolutions :
    (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*nativeEvenJets 0 = -nativeEvenJets 1 ∧
    (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)*nativeEvenJets 0 +
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*nativeEvenJets 1 = -2*nativeEvenJets 2 ∧
    (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ)*nativeEvenJets 0 +
      (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)*nativeEvenJets 1 +
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*nativeEvenJets 2 = -3*nativeEvenJets 3 := by
  have h0 := completedNativeGreenResponse_oddCoefficient_fullConvolution 0
  have h1 := completedNativeGreenResponse_oddCoefficient_fullConvolution 1
  have h2 := completedNativeGreenResponse_oddCoefficient_fullConvolution 2
  norm_num [Finset.sum_range_succ,completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical,
    nativeEvenJets] at h0 h1 h2 ⊢
  exact ⟨h0,by linear_combination h1,by linear_combination h2⟩

/-- A purely algebraic extraction, valid even when v0=0. It is not a division at zero. -/
theorem determinant_clear_of_convolutions (v : Fin 4 → ℂ) (h0 h1 h2 : ℂ)
    (h01 : h0*v 0 = -v 1)
    (h12 : h1*v 0+h0*v 1 = -2*v 2)
    (h23 : h2*v 0+h1*v 1+h0*v 2 = -3*v 3) :
    (v 0)^4*(h0*h2-h1^2) = quartic v := by
  have e1 : v 1 = -h0*v 0 := by linear_combination h01
  have e2 : v 2 = (h0^2-h1)*v 0/2 := by
    rw [e1] at h12
    linear_combination (1/2:ℂ)*h12
  have e3 : v 3 = (-h0^3/6+h0*h1/2-h2/3)*v 0 := by
    rw [e1,e2] at h23
    linear_combination (1/3:ℂ)*h23
  unfold quartic polarizedQuartic
  rw [e1,e2,e3]
  ring

/-- The exact canonical H2 determinant, cleared with the full source value.
The denominator does not depend on a cutoff head. -/
theorem native_two_even_determinant_clear :
    (nativeEvenJets 0)^4 *
      (((canonicalCompletedNativeLogDerivativeMoment 0 : ℝ)*canonicalCompletedNativeLogDerivativeMoment 2-
        (canonicalCompletedNativeLogDerivativeMoment 1)^2 : ℝ) : ℂ) = quartic nativeEvenJets := by
  rcases native_three_convolutions with ⟨h0,h1,h2⟩
  simpa only [Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow] using
    determinant_clear_of_convolutions nativeEvenJets _ _ _ h0 h1 h2

/-- In the normalization of PR66, b1*b5-b3^2 is four times this determinant. -/
theorem response_two_even_determinant (M P : ℕ) :
    (iteratedDeriv 1 (CarryTfvdJoint.centeredPolarizedReadout M P) 0/(1:ℂ))*
      (iteratedDeriv 5 (CarryTfvdJoint.centeredPolarizedReadout M P) 0/(120:ℂ))-
    (iteratedDeriv 3 (CarryTfvdJoint.centeredPolarizedReadout M P) 0/(6:ℂ))^2 =
      4 * (((canonicalCompletedNativeLogDerivativeMoment 0 : ℝ)*canonicalCompletedNativeLogDerivativeMoment 2-
        (canonicalCompletedNativeLogDerivativeMoment 1)^2 : ℝ) : ℂ) := by
  have h0 := CarryTfvdJoint.centeredPolarizedReadout_odd_coefficient M P 0
  have h1 := CarryTfvdJoint.centeredPolarizedReadout_odd_coefficient M P 1
  have h2 := CarryTfvdJoint.centeredPolarizedReadout_odd_coefficient M P 2
  norm_num at h0 h1 h2
  rw [iteratedDeriv_one,div_one,h0,h1,h2]
  push_cast
  ring

end
end CarryTwoEvenJets
