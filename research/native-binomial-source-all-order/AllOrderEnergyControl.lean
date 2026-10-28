import FullSourceTransport

namespace CarryNativeBinomial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarryCriticalComplete CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The existing native all-finite-order error estimate now has explicit
source coefficients; a single threshold serves every input at the fixed n. -/
theorem source_explicit_energy_control_all_order (n : ℕ) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x : ℕ →₀ ℂ, x.support ⊆ Finset.range (2*n) →
      |4*(canonicalCompletedNativeProjectiveChiralForm
          (physicalCompletedFiniteSource k x) (physicalCompletedFiniteSource k x)).re-
        nativeSourceFiniteBoundaryEnergy (2*n) (newtonCoordinates n k (fun r : Fin (2*n) => x r))|≤
          ε*‖newtonCoordinates n k (fun r : Fin (2*n) => x r)‖^2 := by
  filter_upwards [storage_one_chiralJetInput_eventually_energy_control n ε he] with k hk
  intro x hx
  have hs := hk (newtonCoordinates n k (fun r : Fin (2*n) => x r))
  change |2*(storage k (nativeSourceChiralJetInput n k
    (newtonCoordinates n k (fun r : Fin (2*n) => x r))) 1).re-_|≤_ at hs
  rw [newton_input_exact] at hs
  change |2*(storage k (fun r : Fin (2*n) => incidentWeight k r*x r) 1).re-_|≤_ at hs
  rw [original_source_storage k (2*n) x hx] at hs
  simpa only [← mul_assoc,show (2:ℝ)*2=4 from by norm_num] using hs

end
end CarryNativeBinomial
