import ResponseDefect

namespace CarryRadialConservative
open CarrySelfAdjointOperator ChiralReturn NativeLaguerre CarryConservativeIntertwiner CarryCriticalRelative
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
local notation "h₀" => canonicalCompletedNativeLogDerivativeMoment 0

theorem first_even_coefficients (k : ℕ) :
    jetCoefficients 1 k firstEvenBoundary=![amp (canonicalCompletedC3RadialTiltPoint k 0),0] := by
  funext j
  fin_cases j <;> simp [jetCoefficients,nativeSourceChiralJetInput,nativeSourceChiralJetInputMatrix,
    firstEvenBoundary,nativeSourceJetOrderPhase,completedGreenForwardWeight,Fin.sum_univ_two]

/-- Both quadratures of the original first odd stencil remain explicit. -/
theorem first_odd_coefficients (k : ℕ) :
    jetCoefficients 1 k firstOddBoundary=
      ![-amp (canonicalCompletedC3RadialTiltPoint k 0)/(step k),
          amp (canonicalCompletedC3RadialTiltPoint k 1)/(step k)] := by
  funext j
  fin_cases j <;> simp [jetCoefficients,nativeSourceChiralJetInput,nativeSourceChiralJetInputMatrix,
    firstOddBoundary,nativeSourceJetOrderPhase,completedGreenForwardWeight,Fin.sum_univ_two,div_eq_mul_inv]

theorem first_odd_scaled_defect_tendsto_zero :
    Tendsto (fun k => observationScale k 1 • nativeDefect k 2 (jetCoefficients 1 k firstOddBoundary))
      atTop (nhds 0) := by
  apply scaled_native_defect_tendsto_zero 1 1 firstOddBoundary (by norm_num)
  intro a ha
  have h := a.isLt
  omega

theorem first_even_port (k : ℕ) :
    conservativePort k 2 (jetCoefficients 1 k firstEvenBoundary)=
      amp (canonicalCompletedC3RadialTiltPoint k 0)*(radialPortCoefficient k 0:ℂ) := by
  rw [first_even_coefficients]
  simp [conservativePort,Fin.sum_univ_two]

theorem first_even_defect (k : ℕ) :
    nativeDefect k 2 (jetCoefficients 1 k firstEvenBoundary)=
      (amp (canonicalCompletedC3RadialTiltPoint k 0)*
        (completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k 0)-
          (radialSymbol k 0:ℂ))) • completedNativeRadialChiralCauchyState k 0 := by
  rw [native_defect_columns,first_even_coefficients]
  simp [Fin.sum_univ_two]

theorem first_even_port_energy_tendsto :
    Tendsto (fun k => ‖conservativePort k 2 (jetCoefficients 1 k firstEvenBoundary)‖^2)
      atTop (nhds 2) := by
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp (radial_port_tendsto 0)
  have h := ((amp_tendsto 0).mul hr).norm.pow 2
  simpa only [Function.comp_def,← first_even_port,norm_mul,mul_pow,central_amp_norm,
    Complex.ofReal_ofNat,show ‖(2:ℂ)‖=(2:ℝ) by norm_num,show (1:ℝ)/2*2^2=2 by norm_num] using h

theorem first_even_balance_tendsto :
    Tendsto (fun k => ‖radialIncidentSynthesis k 2 (jetCoefficients 1 k firstEvenBoundary)‖^2-
      ‖radialReturnedSynthesis k 2 (jetCoefficients 1 k firstEvenBoundary)‖^2) atTop (nhds (2*h₀)) := by
  have h := (nativeSourceProjectiveBoundaryJetSynthesis_energy_tendsto 1 firstEvenBoundary).div_const 2
  rw [first_even_boundary_energy] at h
  have he : 4*h₀/2=2*h₀ := by ring
  rw [he] at h
  simpa only [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,jetCoefficients,
    mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using h

theorem inverse_radial_sqrt_tendsto :
    Tendsto (fun k : ℕ => (Real.sqrt ((k:ℝ)+1))⁻¹) atTop (nhds 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp real_radial_step_tendsto
  simpa only [Function.comp_def,realRadialStep,Real.sqrt_inv,Real.sqrt_zero] using h

/-- Exact factorization of the ORIGINAL vector error, not an energy approximation. -/
theorem first_even_defect_factor (k : ℕ) :
    nativeDefect k 2 (jetCoefficients 1 k firstEvenBoundary)=
      ((((k:ℝ)+1):ℂ)*
        (completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k 0)-
          (radialSymbol k 0:ℂ))*amp (canonicalCompletedC3RadialTiltPoint k 0)*
          (Real.sqrt ((k:ℝ)+1):ℂ)⁻¹) • completedNativeChiralCauchyFeature 0 := by
  rw [first_even_defect,completedNativeRadialChiralCauchyState,smul_smul]
  congr 1
  have hs : (Real.sqrt ((k:ℝ)+1):ℂ)≠0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0<(k:ℝ)+1)).ne'
  have hsq : (Real.sqrt ((k:ℝ)+1):ℂ)^2=(((k:ℝ)+1):ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0≤(k:ℝ)+1)
  field_simp
  linear_combination (amp (canonicalCompletedC3RadialTiltPoint k 0)*
    (completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k 0)-
      (radialSymbol k 0:ℂ)))*hsq

/-- Here the UNNORMALIZED vector error itself tends to zero. -/
theorem first_even_defect_tendsto_zero :
    Tendsto (fun k => nativeDefect k 2 (jetCoefficients 1 k firstEvenBoundary)) atTop (nhds 0) := by
  have hs := Complex.continuous_ofReal.continuousAt.tendsto.comp inverse_radial_sqrt_tendsto
  have ht := (((native_symbol_defect_tangent 0).mul (amp_tendsto 0)).mul hs).smul_const
    (completedNativeChiralCauchyFeature 0)
  simpa only [← first_even_defect_factor,Function.comp_def,Complex.ofReal_inv,
    Complex.ofReal_zero,mul_zero,zero_smul] using ht

/-- Vanishing vector error does NOT erase its cross with the growing incident channel. -/
theorem first_even_mixed_cross_tendsto :
    Tendsto (fun k => 2*(inner ℂ (conservativeSynthesis k 2 (jetCoefficients 1 k firstEvenBoundary))
      (nativeDefect k 2 (jetCoefficients 1 k firstEvenBoundary))).re) atTop (nhds (2*(1-h₀))) := by
  have he := first_even_defect_tendsto_zero.norm.pow 2
  have ht := (first_even_port_energy_tendsto.sub first_even_balance_tendsto).sub he
  convert ht using 1
  · funext k
    have h := native_energy_ledger k 2 (jetCoefficients 1 k firstEvenBoundary)
    linarith
  · simp
    ring


end
end CarryRadialConservative
