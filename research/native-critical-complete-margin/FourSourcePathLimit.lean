import CriticalBoundaryTransport
namespace CarryCriticalComplete
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- Exact analytic source expression for EVERY physical four-address input,
with the same remainder R and one common radial threshold. No sign premise. -/
theorem physical_boundary_regularized :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ k : ℕ in atTop,
      ∀ x : ℕ →₀ ℂ, x.support ⊆ Finset.range 4 →
        2*(canonicalCompletedNativeProjectiveChiralForm
          (physicalCompletedFiniteSource k x) (physicalCompletedFiniteSource k x)).re=
          radialFourRegularizedStorage R (radialFourSourceStep k) (sourceBoundary k x) := by
  obtain ⟨R,hRa,hE⟩ := storage_one_fourSample_eventually_regularized
  refine ⟨R,hRa,?_⟩
  filter_upwards [hE,canonicalCompletedNativeRadialProjectiveChiral_eventually_regular 4] with k hk hreg
  intro x hx
  have hp := hk (sourceBoundary k x)
  change (storage k (radialCompletedInputCoefficients k
    (radialFourNormalizedBoundaryInput (radialFourSourceStep k)
      (radialFourScaledBoundary (radialFourSourceStep k) (physicalValues k 4 x)))) 1).re=_ at hp
  rw [radialFourNormalizedBoundaryInput_scaled _ (radialFourSourceStep_pos k).ne',
    physical_values_recover k 4 x (fun i => (hreg i).2.1) (fun i => (hreg i).2.2)] at hp
  change (storage k (fun i : Fin 4 => incidentWeight k i*x i) 1).re=_ at hp
  rw [original_source_storage k 4 x hx] at hp
  exact hp

/-- Source-first path-limit theorem: complete boundary VECTOR convergence
controls the original full energy, including the exact analytic remainder.
It assumes no positivity, canonical moments, or bound on the raw coefficients. -/
theorem four_source_path_energy_tendsto (x : ℕ → ℕ →₀ ℂ) (v : Fin 4 → ℂ)
    (hx : ∀ k, (x k).support ⊆ Finset.range 4)
    (hv : Tendsto (fun k => sourceBoundary k (x k)) atTop (nhds v)) :
    Tendsto (fun k : ℕ => (canonicalCompletedNativeProjectiveChiralForm
      (physicalCompletedFiniteSource k (x k)) (physicalCompletedFiniteSource k (x k))).re)
      atTop (nhds (nativeSourceFourBoundaryEnergy v/2)) := by
  obtain ⟨R,hRa,hE⟩ := physical_boundary_regularized
  have ht := (radialFourRegularizedStorage_continuousAt R hRa.continuousAt v).tendsto.comp
    (radialFourSourceStep_tendsto_zero.prodMk_nhds hv)
  have hlim : Tendsto (fun k : ℕ =>
      radialFourRegularizedStorage R (radialFourSourceStep k) (sourceBoundary k (x k))/2)
      atTop (nhds (nativeSourceFourBoundaryEnergy v/2)) := by
    simpa only [Function.comp_def,radialFourRegularizedStorage_zero] using ht.div_const 2
  apply hlim.congr'
  filter_upwards [hE] with k hk
  have he := hk (x k) (hx k)
  linarith

end
end CarryCriticalComplete
