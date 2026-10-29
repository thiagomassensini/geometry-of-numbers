import MixedRadialJets
import CarrySelfAdjointOperator.CompletedGreenForwardDifferenceVectorLimit

namespace CarryMixedRadial
open CarrySelfAdjointOperator CarryCompletedTrace Filter Topology
open scoped ComplexConjugate
noncomputable section
set_option autoImplicit false

/-- Joint analytic kernel limit, for independently moving original nodes. -/
theorem native_kernel_limit {α : Type*} {f : Filter α} {u v : α → ℕ}
    (hu : Tendsto u f atTop) (hv : Tendsto v f atTop) :
    Tendsto (fun a => canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialTiltPoint (u a) 0)
      (canonicalCompletedC3RadialTiltPoint (v a) 0)) f
      (nhds (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) := by
  have hz := (canonicalCompletedC3RadialTiltPoint_tendsto_zero 0).comp hu
  have hw := (canonicalCompletedC3RadialTiltPoint_tendsto_zero 0).comp hv
  have hc : Tendsto (fun a => conj (canonicalCompletedC3RadialTiltPoint (u a) 0)) f
      (nhds (0 : ℂ)) := by
    simpa only [map_zero,Function.comp_def] using
      Complex.continuous_conj.continuousAt.tendsto.comp hz
  have hp := hc.prodMk_nhds hw
  have h := (completedGreenDslope_tendsto_prod_of_analyticAt
    completedNativeGreenNormalizedResponse_analyticAt).comp hp
  have he : deriv (completedGreenNormalizedResponse completedNativeOperatorCharacteristic
      completedNativeOperatorBoundaryCompanion) 0 =
      (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ) := by
    simpa [completedNativeGreenResponseTaylorCoefficient,iteratedDeriv_one] using
      completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical 0
  simpa only [he,canonicalCompletedNativePolarizedDslopeKernel,Function.comp_def,
    map_zero] using h

/-- The geometric factor survives the full completed synthesis and the limit.
Its convergence is geometric input, not a sign assumption on moments. -/
theorem zero_pairing_limit_of_factor {α : Type*} {f : Filter α} {u v : α → ℕ} {ρ : ℝ}
    (hu : Tendsto u f atTop) (hv : Tendsto v f atTop)
    (hρ : Tendsto (fun a => crossRadialFactor (u a) (v a) 0 0) f (nhds ρ)) :
    Tendsto (fun a => zeroPairing (u a) (v a)) f
      (nhds ((ρ : ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  have hr := canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 1
  have heq : (fun a => zeroPairing (u a) (v a)) =ᶠ[f]
      (fun a => (crossRadialFactor (u a) (v a) 0 0 : ℂ)*
        canonicalCompletedNativePolarizedDslopeKernel
          (canonicalCompletedC3RadialTiltPoint (u a) 0)
          (canonicalCompletedC3RadialTiltPoint (v a) 0)) := by
    filter_upwards [hu.eventually hr,hv.eventually hr] with a ha hb
    exact zero_pairing_factor_kernel _ _ (ha 0).1 (ha 0).2.1 (hb 0).2.1
      (ha 0).2.2 (hb 0).2.2
  exact ((Filter.tendsto_ofReal_iff.mpr hρ).mul (native_kernel_limit hu hv)).congr' heq.symm

theorem diagonal_zero_limit : Tendsto (fun k => zeroPairing k k) atTop
    (nhds (canonicalCompletedNativeLogDerivativeMoment 0 : ℂ)) := by
  have h := zero_pairing_limit_of_factor tendsto_id tendsto_id
    (by simpa only [cross_factor_same_radial] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)))
  simpa using h

theorem doubled_index_tendsto : Tendsto (fun k : ℕ => 2*k+1) atTop atTop :=
  tendsto_atTop_mono (fun k => by dsimp; omega) tendsto_id

theorem doubled_zero_limit : Tendsto (fun k => zeroPairing k (2*k+1)) atTop
    (nhds (((3*Real.sqrt 2/4 : ℝ) : ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  exact zero_pairing_limit_of_factor tendsto_id doubled_index_tendsto
    (by simpa only [doubled_zero_factor] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 3*Real.sqrt 2/4) atTop (nhds _)))

theorem doubled_difference_limit : Tendsto (fun k => differencePairing k (2*k+1)) atTop
    (nhds (((2-3*Real.sqrt 2/2 : ℝ) : ℂ)*(canonicalCompletedNativeLogDerivativeMoment 0 : ℂ))) := by
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp doubled_zero_limit
  simp only [Function.comp_def,zero_pairing_conj,map_mul,Complex.conj_ofReal] at hc
  have h := ((diagonal_zero_limit.add (diagonal_zero_limit.comp doubled_index_tendsto)).sub
    doubled_zero_limit).sub hc
  convert h using 1
  · ext k
    exact difference_pairing_four_crosses k (2*k+1)
  · push_cast
    ring

end
end CarryMixedRadial
