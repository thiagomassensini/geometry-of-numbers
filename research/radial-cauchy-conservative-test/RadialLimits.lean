import NativeDefect

namespace CarryRadialConservative
open CarrySelfAdjointOperator ChiralReturn NativeLaguerre CarryConservativeIntertwiner CarryCriticalRelative
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Real reciprocal radial coordinate; its complex lift is the existing Green step. -/
def realRadialStep (k : ℕ) : ℝ := ((k:ℝ)+1)⁻¹

theorem real_radial_step_tendsto : Tendsto realRadialStep atTop (nhds 0) := by
  change Tendsto (fun k : ℕ => ((k:ℝ)+1)⁻¹) atTop (nhds 0)
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))

theorem radial_symbol_in_step (k j : ℕ) :
    radialSymbol k j=(2*((j:ℝ)+1)*realRadialStep k-1)/
      (2*((j:ℝ)+1)*realRadialStep k+1) := by
  rw [radial_symbol_scaled_address]
  simp only [realRadialStep,div_eq_mul_inv,mul_assoc]

theorem radial_port_in_step (k j : ℕ) :
    radialPortCoefficient k j=2/(1+2*((j:ℝ)+1)*realRadialStep k) := by
  have hk : (k:ℝ)+1≠0 := by positivity
  have hd : 1+2*((j:ℝ)+1)*realRadialStep k≠0 := by
    unfold realRadialStep
    positivity
  unfold radialPortCoefficient realRadialStep at *
  field_simp
  ring

theorem radial_symbol_tendsto (j : ℕ) :
    Tendsto (fun k : ℕ => radialSymbol k j) atTop (nhds (-1)) := by
  simp_rw [radial_symbol_in_step]
  have ht := real_radial_step_tendsto.const_mul (2*((j:ℝ)+1))
  have h := (ht.sub_const 1).div (ht.add_const 1) (by norm_num)
  convert h using 1 <;> norm_num
  ext k
  simp only [Pi.div_apply]

theorem radial_port_tendsto (j : ℕ) :
    Tendsto (fun k : ℕ => radialPortCoefficient k j) atTop (nhds 2) := by
  simp_rw [radial_port_in_step]
  have ht := (real_radial_step_tendsto.const_mul (2*((j:ℝ)+1))).const_add 1
  have h := (tendsto_const_nhds (x:=(2:ℝ))).div ht (by norm_num)
  convert h using 1 <;> norm_num
  ext k
  simp only [Pi.div_apply]

/-- First radial coefficient, not merely convergence to the center. -/
theorem radial_symbol_tangent (j : ℕ) :
    Tendsto (fun k : ℕ => (((k:ℝ)+1):ℂ)*((radialSymbol k j:ℂ)+1)) atTop
      (nhds (4*((j:ℂ)+1))) := by
  have hs : Tendsto (fun k : ℕ => (4*((j:ℝ)+1))/(1+2*((j:ℝ)+1)*realRadialStep k)) atTop
      (nhds (4*((j:ℝ)+1))) := by
    have ht := (real_radial_step_tendsto.const_mul (2*((j:ℝ)+1))).const_add 1
    have h := (tendsto_const_nhds (x:=4*((j:ℝ)+1))).div ht (by norm_num)
    convert h using 1 <;> norm_num
    ext k
    simp only [Pi.div_apply]
  have he (k : ℕ) : ((k:ℝ)+1)*(radialSymbol k j+1)=
      (4*((j:ℝ)+1))/(1+2*((j:ℝ)+1)*realRadialStep k) := by
    have hk : (k:ℝ)+1≠0 := by positivity
    have hd : 1+2*((j:ℝ)+1)*realRadialStep k≠0 := by unfold realRadialStep; positivity
    unfold radialSymbol realRadialStep at *
    field_simp
    ring
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,← he,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_one,
    Complex.ofReal_ofNat,Complex.ofReal_natCast] using hc

/-- The source tangent is inherited from the completed characteristic. -/
theorem native_symbol_tangent (j : ℕ) :
    Tendsto (fun k : ℕ => (((k:ℝ)+1):ℂ)*
      (completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)+1))
      atTop (nhds (4*((j:ℂ)+1)*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ))) := by
  have ht := nativeRadialSource_tangent j
  have hr : nativeRadialSourceCurvature=4*(canonicalCompletedNativeLogDerivativeMoment 0:ℂ) := by
    rw [canonicalCompletedNativeLogDerivativeMoment_zero_eq_characteristicCurvature_chiral]
    unfold nativeRadialSourceCurvature
    ring
  rw [hr] at ht
  have hc := ht.const_mul ((j:ℂ)+1)
  convert hc using 1
  · funext k
    have hk : (((k:ℝ)+1):ℂ)≠0 := by exact_mod_cast (show (k:ℝ)+1≠0 by positivity)
    have hj : ((j:ℂ)+1)≠0 := by exact_mod_cast (show (j:ℝ)+1≠0 by positivity)
    unfold canonicalCompletedC3RadialTiltPoint canonicalCompletedC3RadialTiltStep canonicalGreenJetStep
    push_cast
    field_simp
  · ring

/-- Exact source/comparator discrepancy in the first surviving radial coefficient. -/
theorem native_symbol_defect_tangent (j : ℕ) :
    Tendsto (fun k : ℕ => (((k:ℝ)+1):ℂ)*
      (completedNativeHermiteBiehlerChiralQuotient (canonicalCompletedC3RadialTiltPoint k j)-
        (radialSymbol k j:ℂ))) atTop
      (nhds (4*((j:ℂ)+1)*((canonicalCompletedNativeLogDerivativeMoment 0:ℂ)-1))) := by
  convert (native_symbol_tangent j).sub (radial_symbol_tangent j) using 1
  · funext k; ring
  · ring

/-- Normalized vectors match at leading order in EVERY fixed jet direction. -/
theorem scaled_comparator_tendsto (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m<2*n)
    (hx : ∀ a : Fin (2*n), m<a.val → x a=0) :
    Tendsto (fun k : ℕ => observationScale k m • conservativeSynthesis k (2*n) (jetCoefficients n k x))
      atTop (nhds (-leadingState n m x hm)) := by
  have ht : Tendsto (fun k : ℕ => fun r : Fin (2*n) =>
      step k^m*nativeSourceChiralJetInput n k x r*(radialSymbol k r:ℂ)) atTop
      (nhds (-leadingCoefficients n m x hm)) := by
    apply tendsto_pi_nhds.mpr
    intro r
    have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp (radial_symbol_tendsto r)
    have h := ((tendsto_pi_nhds.mp (scaled_input_tendsto n m x hm hx)) r).mul hr
    simpa only [Function.comp_def,Complex.ofReal_neg,Complex.ofReal_one,mul_neg,mul_one,Pi.neg_apply] using h
  have hc : Continuous (radialIncidentSynthesis 0 (2*n)) := LinearMap.continuous_of_finiteDimensional _
  have h := hc.continuousAt.tendsto.comp ht
  have he (k : ℕ) : conservativeSynthesis k (2*n) (jetCoefficients n k x)=
      radialIncidentSynthesis k (2*n) (fun r => nativeSourceChiralJetInput n k x r*(radialSymbol k r:ℂ)) := by
    simp only [conservativeSynthesis,jetCoefficients,radialIncidentSynthesis,LinearMap.coe_mk,AddHom.coe_mk,smul_smul]
  simpa only [he,synthesis_scale,leadingState,map_neg,mul_assoc,Function.comp_def] using h

theorem scaled_native_defect_tendsto_zero (n m : ℕ) (x : Fin (2*n) → ℂ) (hm : m<2*n)
    (hx : ∀ a : Fin (2*n), m<a.val → x a=0) :
    Tendsto (fun k : ℕ => observationScale k m • nativeDefect k (2*n) (jetCoefficients n k x)) atTop (nhds 0) := by
  have h := (scaled_returned_tendsto n m x hm hx).sub (scaled_comparator_tendsto n m x hm hx)
  simpa only [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,nativeDefect,
    jetCoefficients,smul_sub,sub_self] using h

end
end CarryRadialConservative
