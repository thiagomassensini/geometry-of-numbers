import PhysicalTfvd
import Quadratures

namespace CarryNativeTfvd
open CarrySelfAdjointOperator CarryVerticalSynthesis
open CPFormal.Analytic.Cp (NativeGpreTowerHilbert)
open GeometryOfNumbers.Analysis.RealCarry
open scoped BigOperators InnerProductSpace lp ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The same finite coefficients in the two EXISTING real native towers. -/
def coefficientQuadratures (c : ℕ →₀ ℂ) : RealQuadrature.Space NativeGpreTowerHilbert :=
  WithLp.toLp 2 (finiteTower (c.mapRange Complex.re (by simp)),
    finiteTower (c.mapRange Complex.im (by simp)))

theorem coefficient_quadratures_fst (c : ℕ →₀ ℂ) (j : ℕ) :
    (coefficientQuadratures c).fst j = (c j).re := by
  change finiteTower (c.mapRange Complex.re _) j = _
  rw [finite_tower_apply]
  rfl

theorem coefficient_quadratures_snd (c : ℕ →₀ ℂ) (j : ℕ) :
    (coefficientQuadratures c).snd j = (c j).im := by
  change finiteTower (c.mapRange Complex.im _) j = _
  rw [finite_tower_apply]
  rfl

theorem coefficient_tower_synthesis (c : ℕ →₀ ℂ) :
    quadratureSynthesis (coefficientQuadratures c) = NativeLaguerre.physicalCauchySynthesis c := by
  rw [quadrature_synthesis_apply]
  change nativeSynthesis (finiteTower (c.mapRange Complex.re _)) +
    Complex.I • nativeSynthesis (finiteTower (c.mapRange Complex.im _)) = _
  rw [native_synthesis_finite, native_synthesis_finite]
  simp only [finiteSource, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapRange_index (f := Complex.re) (g := c)
      (h := fun j a => (a : ℝ) • completedNativeChiralCauchyFeature j)
      (fun j => zero_smul ℝ (completedNativeChiralCauchyFeature j)),
    Finsupp.sum_mapRange_index (f := Complex.im) (g := c)
      (h := fun j a => (a : ℝ) • completedNativeChiralCauchyFeature j)
      (fun j => zero_smul ℝ (completedNativeChiralCauchyFeature j))]
  simp only [NativeLaguerre.physicalCauchySynthesis, Finsupp.linearCombination_apply,
    Finsupp.sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_eq_complex_ofReal, smul_smul, ← add_smul]
  congr 1
  simpa only [mul_comm] using Complex.re_add_im (c j)

theorem coefficient_real_bracket (eta : ℝ) (c : ℕ →₀ ℂ) :
    carryWeightedVerticalCenteredBracket eta (coefficientQuadratures c).fst =
      (coefficientQuadratures (NativeCauchyPorts.finiteTfvdBulk eta c)).fst := by
  apply lp.ext; funext j
  cases j with
  | zero => simp [coefficient_quadratures_fst, NativeCauchyPorts.finiteTfvdBulk_zero]
  | succ j =>
    simp [carryWeightedVerticalCenteredBracket_succ, coefficient_quadratures_fst,
      NativeCauchyPorts.finiteTfvdBulk_succ, Complex.mul_re,
      ← Complex.ofReal_inv]

theorem coefficient_imag_bracket (eta : ℝ) (c : ℕ →₀ ℂ) :
    carryWeightedVerticalCenteredBracket eta (coefficientQuadratures c).snd =
      (coefficientQuadratures (NativeCauchyPorts.finiteTfvdBulk eta c)).snd := by
  apply lp.ext; funext j
  cases j with
  | zero => simp [coefficient_quadratures_snd, NativeCauchyPorts.finiteTfvdBulk_zero]
  | succ j =>
    simp [carryWeightedVerticalCenteredBracket_succ, coefficient_quadratures_snd,
      NativeCauchyPorts.finiteTfvdBulk_succ, Complex.mul_im,
      ← Complex.ofReal_inv]

/-- Both real reconstructions combine into the original complex finite source,
including the two independent complex traces, before signed pairing. -/
theorem physical_finite_reconstruction (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1)
    (c : ℕ →₀ ℂ) :
    NativeLaguerre.physicalCauchySynthesis c =
      NativeLaguerre.physicalGreenOperator eta h0.le h1
        (NativeLaguerre.physicalCauchySynthesis (NativeCauchyPorts.finiteTfvdBulk eta c)) +
      ((NativeLaguerre.physicalGreenResolvent eta h0.le h1)^2)
        ((c 0) • completedNativeChiralCauchyFeature 0 +
          (c 1 - 2 * (eta : ℂ) * c 0) • completedNativeChiralCauchyFeature 1) := by
  rw [← coefficient_tower_synthesis c, quadrature_synthesis_apply,
    physical_tfvd_reconstruction eta h0 h1 (coefficientQuadratures c).fst,
    physical_tfvd_reconstruction eta h0 h1 (coefficientQuadratures c).snd,
    coefficient_real_bracket, coefficient_imag_bracket,
    ← coefficient_tower_synthesis (NativeCauchyPorts.finiteTfvdBulk eta c),
    quadrature_synthesis_apply]
  simp only [coefficient_quadratures_fst, coefficient_quadratures_snd,
    map_add, map_smul, ContinuousLinearMap.map_smul_of_tower]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  rw [← Complex.re_add_im (c 0), ← Complex.re_add_im (c 1)]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add, add_zero, sub_zero]
  module

end
end CarryNativeTfvd
