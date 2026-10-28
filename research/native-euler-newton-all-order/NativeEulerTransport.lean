import EulerNewtonMatrix
import FullSourceTransport

namespace CarryEulerNewtonAll
open CarrySelfAdjointOperator CarryNativeBinomial CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarryCriticalComplete CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The existing Euler jet read from the original completed value chart. -/
def physicalEulerChart (n k : ℕ) (x : ℕ →₀ ℂ) (j : Fin (2*n)) : ℂ :=
  (radialFourSourceStep k:ℂ)^(j:ℕ)*
    radialEulerBoundaryJet (physicalValues k (2*n) x) j

theorem physical_euler_eq (n k : ℕ) (x : ℕ →₀ ℂ)
    (hF : ∀ i : Fin (2*n), completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    physicalEulerChart n k x=eulerChart (2*n) (radialFourSourceStep k) (fun r : Fin (2*n) => x r) := by
  funext j
  simp only [physicalEulerChart, physical_values_eq k (2*n) x hF hP,
    eulerChart, radialEulerBoundaryJet, Nat.cast_add, Nat.cast_one]

/-- Commuting Euler-Newton diagram for the SAME completed physical values. -/
theorem source_euler_newton_all_order (n k : ℕ) (x : ℕ →₀ ℂ)
    (hF : ∀ i : Fin (2*n), completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    eulerNewton (2*n) (radialFourSourceStep k) (physicalEulerChart n k x)=
      newtonCoordinates n k (fun r : Fin (2*n) => x r) := by
  rw [physical_euler_eq n k x hF hP, euler_newton_raw_exact]

theorem source_euler_newton_eventually_all_order (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ x : ℕ →₀ ℂ,
      eulerNewton (2*n) (radialFourSourceStep k) (physicalEulerChart n k x)=
        newtonCoordinates n k (fun r : Fin (2*n) => x r) := by
  filter_upwards [canonicalCompletedNativeRadialProjectiveChiral_eventually_regular (2*n)] with k hk
  intro x
  exact source_euler_newton_all_order n k x (fun i => (hk i).2.1) (fun i => (hk i).2.2)

/-- Both complete physical channels are preserved before scalar readout. -/
theorem physical_source_euler_all_order (n k : ℕ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range (2*n))
    (hF : ∀ i : Fin (2*n), completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    physicalCompletedFiniteSource k x=nativeSourceProjectiveBoundaryJetSynthesis n k
      (eulerNewton (2*n) (radialFourSourceStep k) (physicalEulerChart n k x)) := by
  rw [source_euler_newton_all_order n k x hF hP]
  exact physical_source_newton_all_order n k x hx

/-- Full complex polarization with two sources, cutoffs and radial indices. -/
theorem physical_pair_euler_all_order (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (n p k l : ℕ) (x y : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range (2*n)) (hy : y.support ⊆ Finset.range (2*p))
    (hxF : ∀ i : Fin (2*n), completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hxP : ∀ i : Fin (2*n), completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hyF : ∀ i : Fin (2*p), completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint l i)≠0)
    (hyP : ∀ i : Fin (2*p), completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint l i)≠0) :
    crossGreenPair eta h0 h1 k l x y=canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis n k
        (eulerNewton (2*n) (radialFourSourceStep k) (physicalEulerChart n k x)))
      (nativeSourceProjectiveBoundaryJetSynthesis p l
        (eulerNewton (2*p) (radialFourSourceStep l) (physicalEulerChart p l y))) := by
  rw [source_euler_newton_all_order n k x hxF hxP,
    source_euler_newton_all_order p l y hyF hyP]
  exact physical_pair_newton_all_order eta h0 h1 n p k l x y hx hy

end
end CarryEulerNewtonAll
