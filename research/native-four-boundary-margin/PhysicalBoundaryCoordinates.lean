import FourSourceBridge
namespace CarryBoundaryMargin
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

/-- Exactly the physical coefficient family in PR119's storage identity. -/
def physicalCoefficients (k N : ℕ) (x : ℕ →₀ ℂ) : Fin N → ℂ :=
  fun i => incidentWeight k i*x i

/-- Existing completed value chart, applied AFTER original physical synthesis. -/
def physicalValues (k N : ℕ) (x : ℕ →₀ ℂ) : Fin N → ℂ :=
  radialCompletedValueCoefficients k (physicalCoefficients k N x)

/-- Cancellation of the prescribed dressing, not a new source normalization. -/
theorem physical_values_eq (k N : ℕ) (x : ℕ →₀ ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    physicalValues k N x = fun i : Fin N => x i/(Real.sqrt 2:ℂ) := by
  funext i
  unfold physicalValues physicalCoefficients radialCompletedValueCoefficients incidentWeight
    completedNativeNormalizedPositiveChiralAmplitude canonicalCompletedC3FullWronskianChiralNormalization
  field_simp [hF i,hP i]

/-- Return to the ORIGINAL input coordinates, so storage is unchanged. -/
theorem physical_values_recover (k N : ℕ) (x : ℕ →₀ ℂ)
    (hF : ∀ i : Fin N, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin N, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    radialCompletedInputCoefficients k (physicalValues k N x)=physicalCoefficients k N x := by
  funext i
  unfold radialCompletedInputCoefficients physicalValues radialCompletedValueCoefficients
  field_simp [hF i,hP i]

/-- Full four-address boundary vector of the SAME completed source. -/
def principalBoundary (a : ℝ) (k : ℕ) : Fin 4 → ℂ :=
  radialFourScaledBoundary (radialFourSourceStep k) (physicalValues k 4 (principalInput a k))

end
end CarryBoundaryMargin
