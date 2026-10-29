import ExactBalance

namespace CarryGreenFinitePart
open CarryInteriorGreen CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def finiteTerm (a : ℝ) : ℝ := canonicalCompletedNativeLogDerivativeMoment 2-
  2*a*canonicalCompletedNativeLogDerivativeMoment 1+a^2*canonicalCompletedNativeLogDerivativeMoment 0

def correctionTerm (a : ℝ) : ℝ := -a^2*canonicalCompletedNativeLogDerivativeMoment 1+
  40*a*canonicalCompletedNativeLogDerivativeMoment 2-14*canonicalCompletedNativeLogDerivativeMoment 3

def fourthPolynomial (a : ℝ) : ℝ := a^2*canonicalCompletedNativeLogDerivativeMoment 2-
  462*a*canonicalCompletedNativeLogDerivativeMoment 3+
  147*canonicalCompletedNativeLogDerivativeMoment 4

/-- The exact analytic error in the SAME complete balance. This is not a
new energy, a changed metric, or a substitute physical source. -/
def remainderReadout (R : ℂ → ℂ) (a t : ℝ) : ℝ :=
  (a^2*t^4+7*a*t^2/12+1/24)*(R (t : ℂ)).re+
  2048*(-2*a*t^2/3-1/30)*(R ((2*t : ℝ) : ℂ)).re+
  177147*(a*t^2/4+1/120)*(R ((3*t : ℝ) : ℂ)).re

def errorReadout (R : ℂ → ℂ) (a t : ℝ) : ℝ :=
  -a^2*canonicalCompletedNativeLogDerivativeMoment 3+
  4580*a*canonicalCompletedNativeLogDerivativeMoment 4+
  t^2*a^2*canonicalCompletedNativeLogDerivativeMoment 4+remainderReadout R a t

/-- Exact after all vector/crossing identities. The same analytic remainder
works for every eta and every free critical-direction coefficient a. -/
theorem green_balance_exact_expansion :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ (η : ℝ), 0<η → η<1 → ∀ a : ℝ,
      ∀ᶠ k : ℕ in atTop, greenBalance η a k=finiteTerm a+
        radialStep k^2*correctionTerm a+radialStep k^4*fourthPolynomial a+
        radialStep k^6*errorReadout R a (radialStep k) := by
  obtain ⟨R,hRa,he⟩ := readout_exact_remainder
  refine ⟨R,hRa,?_⟩
  intro η hη0 hη1 a
  have ht (j : ℕ) : Tendsto (fun (k : ℕ) => (((j+1 : ℕ) : ℂ)*(radialStep k : ℂ)))
      atTop (nhds 0) := by
    have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_limit
    simpa only [Function.comp_def,Complex.ofReal_zero,mul_zero] using hs.const_mul (((j+1 : ℕ) : ℂ))
  filter_upwards [(ht 0).eventually he,(ht 1).eventually he,(ht 2).eventually he,
    three_regular_eventually] with k h0 h1 h2 hreg
  rw [green_balance_three_samples η hη0 hη1 a k hreg]
  simp only [radial_node_readout]
  have hs0 := congrArg Complex.re h0
  have hs1 := congrArg Complex.re h1
  have hs2 := congrArg Complex.re h2
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_pow,
    Complex.add_re,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,zero_mul,sub_zero] at hs0 hs1 hs2
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_mul]
  rw [hs0,hs1,hs2]
  norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_add,one_mul]
  unfold finiteTerm correctionTerm errorReadout fourthPolynomial remainderReadout radialStep
  generalize hk : (k : ℝ)+1=K
  have hK : K≠0 := by rw [← hk]; positivity
  field_simp [hK]
  push_cast
  ring

def criticalParameter : ℝ := canonicalCompletedNativeLogDerivativeMoment 1/
  canonicalCompletedNativeLogDerivativeMoment 0

theorem finite_term_critical (h0 : canonicalCompletedNativeLogDerivativeMoment 0≠0) :
    finiteTerm criticalParameter=sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 0 1 := by
  rw [first_source_schur_eq]
  unfold finiteTerm criticalParameter
  field_simp [h0]
  ring

theorem critical_correction_formula (h0 : canonicalCompletedNativeLogDerivativeMoment 0≠0) :
    correctionTerm criticalParameter=
      -(canonicalCompletedNativeLogDerivativeMoment 1^3-
        40*canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 1*
          canonicalCompletedNativeLogDerivativeMoment 2+
        14*canonicalCompletedNativeLogDerivativeMoment 0^2*canonicalCompletedNativeLogDerivativeMoment 3)/
      canonicalCompletedNativeLogDerivativeMoment 0^2 := by
  unfold correctionTerm criticalParameter
  field_simp [h0]
  ring

end
end CarryGreenFinitePart
