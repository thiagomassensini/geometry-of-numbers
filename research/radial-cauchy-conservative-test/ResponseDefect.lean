import RadialLimits
import CarrySelfAdjointOperator.CompletedNativeChiralCayleyHerglotz

namespace CarryRadialConservative
open CarrySelfAdjointOperator ChiralReturn
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem cayley_difference (a b : ℂ) (ha : a+Complex.I≠0) (hb : b+Complex.I≠0) :
    (a-Complex.I)/(a+Complex.I)-(b-Complex.I)/(b+Complex.I)=
      2*Complex.I*(a-b)/((a+Complex.I)*(b+Complex.I)) := by
  field_simp
  ring

/-- This comparator Cayley-transforms the ADDRESS coordinate 2z, not the completed response. -/
theorem radial_symbol_cayley (k j : ℕ) :
    (radialSymbol k j:ℂ)=
      (2*canonicalCompletedC3RadialTiltPoint k j-Complex.I)/
        (2*canonicalCompletedC3RadialTiltPoint k j+Complex.I) := by
  rw [radial_symbol_scaled_address]
  have hz : canonicalCompletedC3RadialTiltPoint k j=
      Complex.I*((((j:ℝ)+1)/((k:ℝ)+1):ℝ):ℂ) := by
    unfold canonicalCompletedC3RadialTiltPoint canonicalCompletedC3RadialTiltStep canonicalGreenJetStep
    push_cast
    ring
  rw [hz]
  rw [show 2*(Complex.I*((((j:ℝ)+1)/((k:ℝ)+1):ℝ):ℂ))-Complex.I=
    Complex.I*(2*((((j:ℝ)+1)/((k:ℝ)+1):ℝ):ℂ)-1) by ring]
  rw [show 2*(Complex.I*((((j:ℝ)+1)/((k:ℝ)+1):ℝ):ℂ))+Complex.I=
    Complex.I*(2*((((j:ℝ)+1)/((k:ℝ)+1):ℝ):ℂ)+1) by ring]
  rw [mul_div_mul_left _ _ Complex.I_ne_zero]
  push_cast
  rfl

/-- Complete native dependence is the defect of -F'/F against the linear address, with no fitted ruler. -/
theorem native_response_defect_on_grid (k j : ℕ)
    (hF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k j)≠0)
    (hp : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k j)≠0) :
    completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)-
      (radialSymbol k j:ℂ)=
    2*Complex.I*(completedNativeLogDerivativeHerglotzCoordinate (canonicalCompletedC3RadialTiltPoint k j)-
      2*canonicalCompletedC3RadialTiltPoint k j)/
      ((completedNativeLogDerivativeHerglotzCoordinate (canonicalCompletedC3RadialTiltPoint k j)+Complex.I)*
        (2*canonicalCompletedC3RadialTiltPoint k j+Complex.I)) := by
  have ha : completedNativeLogDerivativeHerglotzCoordinate (canonicalCompletedC3RadialTiltPoint k j)+Complex.I≠0 := by
    intro hz
    apply hp
    rw [completedNativePositiveHermiteBiehlerCoordinate_eq_characteristic_mul_herglotz_add_I hF,hz,mul_zero]
  have hb : 2*canonicalCompletedC3RadialTiltPoint k j+Complex.I≠0 := by
    intro hz
    have he := congrArg Complex.im hz
    norm_num [Complex.add_im,Complex.mul_im,canonicalCompletedC3RadialTiltPoint_im] at he
    have hh : 0<((j:ℝ)+1)*((k:ℝ)+1)⁻¹ := by positivity
    linarith
  rw [radial_symbol_cayley,completedNativeHermiteBiehlerChiralQuotient_eq_cayley hF]
  exact cayley_difference _ _ ha hb

end
end CarryRadialConservative
