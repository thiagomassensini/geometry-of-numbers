import FiveKernel

namespace CarryPolarizedFour
open CarryGreenFinitePart CarryInteriorGreen CarryFirstOddGreen CarryFiniteGreen CarryRadialGreen
open CarryMeanContrast CarryRadialRefinement CarryPhysicalTrace CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def momentPairing (m : ℕ → ℝ) (u v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, u i*v j*m (i.val+j.val)

def finiteTerm (u v : Fin 3 → ℝ) : ℝ := momentPairing canonicalCompletedNativeLogDerivativeMoment u v

def correctionTerm (u v : Fin 3 → ℝ) : ℝ :=
  -crosses u v 0*canonicalCompletedNativeLogDerivativeMoment 1-
  20*crosses u v 1*canonicalCompletedNativeLogDerivativeMoment 2-
  (126*crosses u v 2+14*crosses u v 3)*canonicalCompletedNativeLogDerivativeMoment 3-
  75*crosses u v 4*canonicalCompletedNativeLogDerivativeMoment 4-
  55*crosses u v 5*canonicalCompletedNativeLogDerivativeMoment 5

def fourthTerm (u v : Fin 3 → ℝ) : ℝ :=
  crosses u v 0*canonicalCompletedNativeLogDerivativeMoment 2+
  231*crosses u v 1*canonicalCompletedNativeLogDerivativeMoment 3+
  (6027*crosses u v 2+147*crosses u v 3)*canonicalCompletedNativeLogDerivativeMoment 4+
  3102*crosses u v 4*canonicalCompletedNativeLogDerivativeMoment 5+
  2002*crosses u v 5*canonicalCompletedNativeLogDerivativeMoment 6

def higherPolynomial (u v : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  (-crosses u v 0*canonicalCompletedNativeLogDerivativeMoment 3-
    2290*crosses u v 1*canonicalCompletedNativeLogDerivativeMoment 4-
    (210232*crosses u v 2+1408*crosses u v 3)*canonicalCompletedNativeLogDerivativeMoment 5-
    101530*crosses u v 4*canonicalCompletedNativeLogDerivativeMoment 6)+
  t^2*(crosses u v 0*canonicalCompletedNativeLogDerivativeMoment 4+
    21461*crosses u v 1*canonicalCompletedNativeLogDerivativeMoment 5+
    (6339333*crosses u v 2+13013*crosses u v 3)*canonicalCompletedNativeLogDerivativeMoment 6)+
  t^4*(-crosses u v 0*canonicalCompletedNativeLogDerivativeMoment 5-
    196560*crosses u v 1*canonicalCompletedNativeLogDerivativeMoment 6)+
  t^6*crosses u v 0*canonicalCompletedNativeLogDerivativeMoment 6

def normalizedMass (u v : Fin 3 → ℝ) (t : ℝ) : Fin 5 → ℝ :=
  ![crosses u v 5/8640-7*t^2*crosses u v 4/2880+
      t^4*(crosses u v 2/45+crosses u v 3/24)-7*t^6*crosses u v 1/24+t^8*crosses u v 0,
    -crosses u v 5/7560+t^2*crosses u v 4/315+
      t^4*(-crosses u v 2/18-crosses u v 3/30)+t^6*crosses u v 1/3,
    crosses u v 5/13440-29*t^2*crosses u v 4/13440+
      t^4*(crosses u v 2/16+crosses u v 3/120)-t^6*crosses u v 1/8,
    -crosses u v 5/45360+t^2*crosses u v 4/1260-t^4*crosses u v 2/30,
    crosses u v 5/362880-t^2*crosses u v 4/8064+t^4*crosses u v 2/144]

/-- Exact error of the SAME original balance, not a substitute energy. -/
def errorReadout (R : ℂ → ℂ) (u v : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  higherPolynomial u v t+∑ j : Fin 5,
    normalizedMass u v t j*(((j.val+1 : ℕ) : ℝ)^15)*(R (((((j.val+1 : ℕ) : ℝ)*t) : ℝ) : ℂ)).re

/-- The original analytic response, with all terms through degree 13 and a
retained analytic remainder. This theorem has no sign premise. -/
theorem readout_fifteenth_remainder :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ t : ℂ in nhds 0,
      imaginaryReadout t=(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)*t-
        (canonicalCompletedNativeLogDerivativeMoment 1 : ℂ)*t^3+
        (canonicalCompletedNativeLogDerivativeMoment 2 : ℂ)*t^5-
        (canonicalCompletedNativeLogDerivativeMoment 3 : ℂ)*t^7+
        (canonicalCompletedNativeLogDerivativeMoment 4 : ℂ)*t^9-
        (canonicalCompletedNativeLogDerivativeMoment 5 : ℂ)*t^11+
        (canonicalCompletedNativeLogDerivativeMoment 6 : ℂ)*t^13+t^15*R t := by
  obtain ⟨R,hRa,he⟩ := readout_analytic.exists_eventuallyEq_sum_add_pow_mul 15
  refine ⟨R,hRa,?_⟩
  filter_upwards [he] with t ht
  rw [ht]
  have hp : (∑ n ∈ Finset.range 15, (t^n/(n.factorial : ℂ)) • iteratedDeriv n imaginaryReadout 0)=
      ∑ n ∈ Finset.range 15, readoutCoefficient n*t^n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [← readout_coefficient_derivative]
    simp only [smul_eq_mul]
    ring
  rw [hp]
  simp only [smul_eq_mul]
  have h0 := readout_coefficient_even 0
  have h1 := readout_coefficient_odd 0
  have h2 := readout_coefficient_even 1
  have h3 := readout_coefficient_odd 1
  have h4 := readout_coefficient_even 2
  have h5 := readout_coefficient_odd 2
  have h6 := readout_coefficient_even 3
  have h7 := readout_coefficient_odd 3
  have h8 := readout_coefficient_even 4
  have h9 := readout_coefficient_odd 4
  have h10 := readout_coefficient_even 5
  have h11 := readout_coefficient_odd 5
  have h12 := readout_coefficient_even 6
  have h13 := readout_coefficient_odd 6
  have h14 := readout_coefficient_even 7
  norm_num only at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14]
  ring

/-- Arbitrary real coefficient vectors in BOTH arguments. The vector
identity and the 25 ordered crossings have already been proved. -/
theorem quartic_exact_expansion :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ (η : ℝ), 0<η → η<1 → ∀ u v : Fin 3 → ℝ,
      ∀ᶠ k : ℕ in atTop, quarticBalance η u v k=finiteTerm u v+
        radialStep k^2*correctionTerm u v+radialStep k^4*fourthTerm u v+
        radialStep k^6*errorReadout R u v (radialStep k) := by
  obtain ⟨R,hRa,he⟩ := readout_fifteenth_remainder
  refine ⟨R,hRa,?_⟩
  intro η hη0 hη1 u v
  have ht (j : ℕ) : Tendsto (fun (k : ℕ) => (((j+1 : ℕ) : ℂ)*(radialStep k : ℂ)))
      atTop (nhds 0) := by
    have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp radial_step_limit
    simpa only [Function.comp_def,Complex.ofReal_zero,mul_zero] using hs.const_mul (((j+1 : ℕ) : ℂ))
  filter_upwards [(ht 0).eventually he,(ht 1).eventually he,(ht 2).eventually he,
    (ht 3).eventually he,(ht 4).eventually he,five_regular_eventually] with k h0 h1 h2 h3 h4 hreg
  rw [quartic_balance_five_samples η hη0 hη1 k hreg]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,add_zero,radial_node_readout]
  have hs0 := congrArg Complex.re h0
  have hs1 := congrArg Complex.re h1
  have hs2 := congrArg Complex.re h2
  have hs3 := congrArg Complex.re h3
  have hs4 := congrArg Complex.re h4
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_mul,← Complex.ofReal_pow,
    Complex.add_re,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,zero_mul,sub_zero] at hs0 hs1 hs2 hs3 hs4
  simp only [← Complex.ofReal_natCast,← Complex.ofReal_mul]
  rw [hs0,hs1,hs2,hs3,hs4]
  unfold finiteTerm momentPairing correctionTerm fourthTerm errorReadout higherPolynomial normalizedMass sampleMass
  norm_num [Fin.sum_univ_succ,crosses]
  unfold radialStep
  generalize hk : (k : ℝ)+1=K
  have hK : K≠0 := by rw [← hk]; positivity
  field_simp [hK]
  push_cast
  ring

end
end CarryPolarizedFour
