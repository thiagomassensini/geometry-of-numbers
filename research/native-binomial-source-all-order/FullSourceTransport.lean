import NativeNewtonInput
import CriticalJetTransport

namespace CarryNativeBinomial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarryCriticalComplete CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Every finite prefix, both original legs, before any scalar readout. -/
theorem physical_source_newton_all_order (n k : ℕ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range (2*n)) :
    physicalCompletedFiniteSource k x=nativeSourceProjectiveBoundaryJetSynthesis n k
      (newtonCoordinates n k (fun r : Fin (2*n) => x r)) := by
  rw [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource, newton_input_exact]
  change physicalCompletedFiniteSource k x=
    (radialIncidentSynthesis k (2*n) (fun r => incidentWeight k r*x r),
      radialReturnedSynthesis k (2*n) (fun r => incidentWeight k r*x r))
  rw [original_source_graph k (2*n) x hx]
  simp only [sourceIncident,weightedIncident,radialIncidentVector_coe,radialReturnTransfer_exact]

/-- Every cutoff containing the same input produces the same ENTIRE physical
state, not just an equal scalar response or equal diagonal energies. -/
theorem native_synthesis_prefix_coherent (n p k : ℕ) (x : ℕ →₀ ℂ)
    (hn : x.support ⊆ Finset.range (2*n)) (hp : x.support ⊆ Finset.range (2*p)) :
    nativeSourceProjectiveBoundaryJetSynthesis n k
      (newtonCoordinates n k (fun r : Fin (2*n) => x r))=
    nativeSourceProjectiveBoundaryJetSynthesis p k
      (newtonCoordinates p k (fun r : Fin (2*p) => x r)) := by
  rw [← physical_source_newton_all_order n k x hn, ← physical_source_newton_all_order p k x hp]

/-- Two independent sources, two cutoffs and two radial indices. No diagonal
norm comparison or discarded Green crossing is used. -/
theorem physical_pair_newton_all_order (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (n m k l : ℕ) (x y : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range (2*n)) (hy : y.support ⊆ Finset.range (2*m)) :
    crossGreenPair eta h0 h1 k l x y=canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k (newtonCoordinates n k (fun r : Fin (2*n) => x r)))
      (nativeSourceProjectiveBoundaryJetSynthesis m l (newtonCoordinates m l (fun r : Fin (2*m) => y r))) := by
  rw [cross_green_eq_original]
  unfold crossSignedPair
  rw [physical_source_newton_all_order n k x hx,physical_source_newton_all_order m l y hy]

/-- Uniqueness uses the existing regular native injectivity; no determinant
or second bijectivity construction is introduced. -/
theorem newton_coordinates_unique (n k : ℕ) (x y : Fin (2*n) → ℂ)
    (hreg : ∀ i : Fin (2*n),
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    nativeSourceChiralJetInput n k y=(fun r : Fin (2*n) => incidentWeight k r*x r) ↔
      y=newtonCoordinates n k x := by
  change nativeSourceChiralJetInput n k y=(fun r : Fin (2*n) =>
    completedNativeNormalizedPositiveChiralAmplitude (canonicalCompletedC3RadialTiltPoint k r)*x r) ↔ _
  rw [← newton_input_exact n k x]
  exact (nativeSourceChiralJetInput_injective n k hreg).eq_iff

/-- Exact regression of PR122's chart, including its phase. -/
theorem four_coordinates_regression (k : ℕ) (x : Fin 4 → ℂ) :
    newtonCoordinates 2 k x=CarryEulerNewton.fourNewtonCoordinates k x := rfl

theorem critical_coordinates_regression (a : ℝ) (k : ℕ) :
    newtonCoordinates 2 k (fun r : Fin 4 => criticalOddSource a k r)=
      CarryEulerNewton.criticalJet a := by
  rw [four_coordinates_regression, CarryEulerNewton.critical_newton_coordinates]

end
end CarryNativeBinomial
