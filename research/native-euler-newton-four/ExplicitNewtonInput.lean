import CriticalBoundaryTransport
import CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport
namespace CarryEulerNewton
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarryCriticalComplete CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Explicit inverse binomial coordinates of the original raw four-address
input. The old phase, factorial and imaginary step are retained literally. -/
def fourNewtonCoordinates (k : ℕ) (x : Fin 4 → ℂ) (m : Fin 4) : ℂ :=
  nativeSourceJetOrderPhase m * ((m:ℕ).factorial:ℂ) *
    canonicalCompletedC3RadialSecondStep k^(m:ℕ) *
      ∑ r : Fin 4, (Nat.choose (r:ℕ) (m:ℕ):ℂ)*x r

/-- Exact coefficient sewing, without choosing a preimage by bijectivity.
The physical projective amplitude occurs once on both sides. No sign premise. -/
theorem four_newton_input_exact (k : ℕ) (x : Fin 4 → ℂ) :
    nativeSourceChiralJetInput 2 k (fourNewtonCoordinates k x)=
      fun r : Fin 4 => incidentWeight k r*x r := by
  have hs := canonicalCompletedC3RadialSecondStep_ne_zero k
  funext r
  fin_cases r <;>
    norm_num [nativeSourceChiralJetInput,nativeSourceChiralJetInputMatrix,
      fourNewtonCoordinates,nativeSourceJetOrderPhase,completedGreenForwardWeight,
      Fin.sum_univ_succ,incidentWeight] <;> field_simp [hs] <;> ring_nf
  all_goals rfl

/-- Regularity is needed for uniqueness, not for the forward coefficient identity. -/
theorem four_newton_coordinates_unique (k : ℕ) (x y : Fin 4 → ℂ)
    (hreg : ∀ i : Fin 4,
      completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0 ∧
      completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    nativeSourceChiralJetInput 2 k y=(fun r : Fin 4 => incidentWeight k r*x r) ↔
      y=fourNewtonCoordinates k x := by
  rw [← four_newton_input_exact k x]
  exact (nativeSourceChiralJetInput_injective 2 k hreg).eq_iff

end
end CarryEulerNewton
