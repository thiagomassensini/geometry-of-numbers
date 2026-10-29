import CubicGreen

namespace CarryCubicTfvd
open CarrySelfAdjointOperator NativeCauchyPorts NativeLaguerre
open CarryNativeTfvd CarryCriticalTfvd CarryCurvatureGreen CarryLinearTfvd CarryStencilBoundary
open CarryCommutatorControl
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Original jets J4-a J2-b J0. The coefficients are free real parameters;
they are not chosen by any moment sign or inverse fitted Gram. -/
def criticalFamily (k : ℕ) (a b : ℝ) : ℕ →₀ ℂ :=
  radialJetCoefficients k 4-(a : ℂ) • radialJetCoefficients k 2-
    (b : ℂ) • radialJetCoefficients k 0

/-- Whole-vector identity in the original TWO completed source channels. -/
theorem critical_family_original_source (k : ℕ) (a b : ℝ) :
    physicalCompletedFiniteSource k (criticalFamily k a b)=
      projectiveChiralDifferenceJet k 4-(a : ℂ) • projectiveChiralDifferenceJet k 2-
        (b : ℂ) • projectiveChiralDifferenceJet k 0 := by
  rw [physicalCompletedFiniteSource_original]
  simp only [criticalFamily, map_sub, map_smul]
  rw [← physicalCompletedFiniteSource_original, ← physicalCompletedFiniteSource_original,
    ← physicalCompletedFiniteSource_original, radial_jet_original_source,
    radial_jet_original_source, radial_jet_original_source]

theorem critical_family_synthesis (k : ℕ) (a b : ℝ) :
    physicalCauchySynthesis (criticalFamily k a b)=
      radialLeadingScalar k 4 • ((physicalComplement^4) (completedNativeChiralCauchyFeature 0))-
      ((a : ℂ)*radialLeadingScalar k 2) • ((physicalComplement^2) (completedNativeChiralCauchyFeature 0))-
      (b : ℂ) • completedNativeChiralCauchyFeature 0 := by
  simp only [criticalFamily, map_sub, map_smul, radial_jet_synthesis, smul_smul]
  norm_num [radialLeadingScalar]

theorem critical_family_two_traces (k : ℕ) (a b : ℝ) :
    criticalFamily k a b 0=radialLeadingScalar k 4-(a : ℂ)*radialLeadingScalar k 2-(b : ℂ) ∧
    criticalFamily k a b 1= -4*radialLeadingScalar k 4+2*(a : ℂ)*radialLeadingScalar k 2 := by
  have h4 := radial_jet_two_traces k 4
  have h2 := radial_jet_two_traces k 2
  have hz := radial_jet_two_traces k 0
  simp only [criticalFamily, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
    h4.1, h4.2, h2.1, h2.2, hz.1, hz.2]
  norm_num only [radialLeadingScalar, pow_zero, mul_one, Nat.factorial_zero,
    Nat.cast_one, inv_one, zero_mul, mul_zero, sub_zero, Nat.cast_ofNat]
  constructor
  · trivial
  · ring

theorem critical_family_cubic_trace (k : ℕ) (a b : ℝ) :
    cubicTrace (criticalFamily k a b)=
      (radialLeadingScalar k 4-(a : ℂ)*radialLeadingScalar k 2-(b : ℂ)) •
        completedNativeChiralCauchyFeature 0 +
      (-28*radialLeadingScalar k 4+14*(a : ℂ)*radialLeadingScalar k 2) •
        completedNativeChiralCauchyFeature 1 := by
  simp only [cubicTrace, (critical_family_two_traces k a b).1,
    (critical_family_two_traces k a b).2]
  module

/-- Concrete five-address test of the same source input, including radial phases. -/
theorem critical_family_explicit (k : ℕ) (a b : ℝ) :
    criticalFamily k a b =
      Finsupp.single 0 (radialLeadingScalar k 4-(a : ℂ)*radialLeadingScalar k 2-(b : ℂ))+
      Finsupp.single 1 (-4*radialLeadingScalar k 4+2*(a : ℂ)*radialLeadingScalar k 2)+
      Finsupp.single 2 (6*radialLeadingScalar k 4-(a : ℂ)*radialLeadingScalar k 2)+
      Finsupp.single 3 (-4*radialLeadingScalar k 4)+Finsupp.single 4 (radialLeadingScalar k 4) := by
  have hc : Nat.choose 4 2=6 := by decide
  ext j
  rcases j with _ | _ | _ | _ | _ | j
  all_goals norm_num [hc, Finsupp.single_apply, criticalFamily, radialJetCoefficients, raw_stencil_apply,
    completedGreenForwardWeight, radialLeadingScalar] <;> ring

theorem critical_family_support (k : ℕ) (a b : ℝ) :
    (criticalFamily k a b).support ⊆ Finset.range 5 := by
  intro j hj
  by_contra hn
  have hge : 5 ≤ j := by simpa using hn
  have hz : criticalFamily k a b j=0 := by
    simp [criticalFamily, radialJetCoefficients, raw_stencil_apply,
      completedGreenForwardWeight, Nat.choose_eq_zero_of_lt (by omega : 4 < j),
      Nat.choose_eq_zero_of_lt (by omega : 2 < j), Nat.choose_eq_zero_of_lt (by omega : 0 < j)]
  exact (Finsupp.mem_support_iff.mp hj) hz

/-- The commutator reaches the OLD exterior address 5; no cutoff at 4 is made. -/
theorem critical_cubic_commutator_support (eta : ℝ) (k : ℕ) (a b : ℝ) :
    (completionCommutator eta (monomialWeight 3) (criticalFamily k a b)).support ⊆ Finset.range 6 := by
  intro j hj
  by_contra hn
  have hge : 6 ≤ j := by simpa using hn
  have hz : completionCommutator eta (monomialWeight 3) (criticalFamily k a b) j=0 := by
    cases j with
    | zero => omega
    | succ j =>
      rw [cubic_commutator_succ,
        coefficient_outside_prefix _ (critical_family_support k a b) (j+2) (by omega),
        coefficient_outside_prefix _ (critical_family_support k a b) j (by omega)]
      simp
  exact (Finsupp.mem_support_iff.mp hj) hz

/-- All NINE ordered complex pairings precede the real diagonal readout.
No symmetry of this generally non-Hermitian kernel is presumed. -/
theorem cubic_three_input_expansion (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (u v w : ℕ →₀ ℂ) (a b : ℝ) :
    (cubicKernel eta h0 h1 (u-(a : ℂ) • v-(b : ℂ) • w)
      (u-(a : ℂ) • v-(b : ℂ) • w)).re =
      (cubicKernel eta h0 h1 u u).re+a^2*(cubicKernel eta h0 h1 v v).re+
      b^2*(cubicKernel eta h0 h1 w w).re-
      a*(cubicKernel eta h0 h1 u v+cubicKernel eta h0 h1 v u).re-
      b*(cubicKernel eta h0 h1 u w+cubicKernel eta h0 h1 w u).re+
      a*b*(cubicKernel eta h0 h1 v w+cubicKernel eta h0 h1 w v).re := by
  simp only [sub_eq_add_neg, ← neg_smul]
  simp only [cubicKernel, sectorKernel, map_add, map_smul, field_add_input,
    field_scale_input, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    map_neg, Complex.conj_ofReal]
  simp only [Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem critical_cubic_expansion (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (k : ℕ) (a b : ℝ) :
    (cubicKernel eta h0 h1 (criticalFamily k a b) (criticalFamily k a b)).re =
      (cubicKernel eta h0 h1 (radialJetCoefficients k 4) (radialJetCoefficients k 4)).re+
      a^2*(cubicKernel eta h0 h1 (radialJetCoefficients k 2) (radialJetCoefficients k 2)).re+
      b^2*(cubicKernel eta h0 h1 (radialJetCoefficients k 0) (radialJetCoefficients k 0)).re-
      a*(cubicKernel eta h0 h1 (radialJetCoefficients k 4) (radialJetCoefficients k 2)+
        cubicKernel eta h0 h1 (radialJetCoefficients k 2) (radialJetCoefficients k 4)).re-
      b*(cubicKernel eta h0 h1 (radialJetCoefficients k 4) (radialJetCoefficients k 0)+
        cubicKernel eta h0 h1 (radialJetCoefficients k 0) (radialJetCoefficients k 4)).re+
      a*b*(cubicKernel eta h0 h1 (radialJetCoefficients k 2) (radialJetCoefficients k 0)+
        cubicKernel eta h0 h1 (radialJetCoefficients k 0) (radialJetCoefficients k 2)).re := by
  exact cubic_three_input_expansion eta h0 h1 _ _ _ a b

end
end CarryCubicTfvd
