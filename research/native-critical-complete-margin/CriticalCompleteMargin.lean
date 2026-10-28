import DefectUniformControl
namespace CarryCriticalComplete
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- Transport of PR120's actual margin to the FULL original critical source.
The correction is bounded, not discarded, uniformly in the real parameter. -/
theorem critical_uniform_physical_margin (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    ∃ ν : ℝ, 0<ν ∧ ∀ᶠ k : ℕ in atTop, ∀ a : ℝ,
      ν*(1+a^2) ≤ (crossGreenPair eta h0 h1 k k
        (criticalOddSource a k) (criticalOddSource a k)).re := by
  obtain ⟨μ,hm,hp⟩ := principal_uniform_physical_margin eta h0 h1
  refine ⟨μ/2,by positivity,?_⟩
  filter_upwards [hp,critical_principal_uniform_close eta h0 h1 (μ/2) (by positivity)] with k hk hc
  intro a
  have hP := hk a
  have hC := hc a a
  rw [abs_of_nonneg (mul_self_nonneg a)] at hC
  simp only [Complex.sub_re] at hC
  have hL := (abs_le.mp hC).1
  nlinarith

/-- Native full-source limit computed from the boundary VECTOR and exact
analytic remainder, independently of the canonical moment readout. -/
theorem critical_native_energy_limit (a : ℝ) (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) :
    Tendsto (fun k : ℕ => (crossGreenPair eta h0 h1 k k
      (criticalOddSource a k) (criticalOddSource a k)).re) atTop
      (nhds (nativeSourceFourBoundaryEnergy (boundaryLimit a)/2)) := by
  have ht := four_source_path_energy_tendsto (criticalOddSource a) (boundaryLimit a)
    (critical_four_support a) (critical_boundary_tendsto a)
  simpa only [cross_green_eq_original] using ht

end
end CarryCriticalComplete
