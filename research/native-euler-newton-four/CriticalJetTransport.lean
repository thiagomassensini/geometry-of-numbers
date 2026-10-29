import EulerNewtonBridge
namespace CarryEulerNewton
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryCommutatorControl CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryMixedParity CarryCrossRadial CarryGreenLeading CarryGreenCubic CarryOddGreen CarryCubicOdd CarryCurvatureGreen CarryOddCauchy CarryCriticalGrid NativeLaguerre NativeCauchyPorts
open CarryAddressSplit CarryPrincipalFlow CarryTailReturn CarryBoundaryMargin CarryCriticalComplete CarrySelfAdjointOperator.ChiralReturn CarrySelfAdjointOperator.PhysicalSewing
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Entire original two-leg state, before any norm or scalar projection. -/
theorem physical_source_newton (k : ℕ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range 4) :
    physicalCompletedFiniteSource k x=nativeSourceProjectiveBoundaryJetSynthesis 2 k
      (fourNewtonCoordinates k (fun r : Fin 4 => x r)) := by
  rw [nativeSourceProjectiveBoundaryJetSynthesis_eq_originalSource,four_newton_input_exact,
    original_source_graph k 4 x hx]
  simp only [sourceIncident,weightedIncident,radialIncidentVector_coe,radialReturnTransfer_exact]

/-- Commuting source/Euler/Newton diagram with the original amplitude ONCE. -/
theorem physical_source_euler (k : ℕ) (x : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range 4)
    (hF : ∀ i : Fin 4, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin 4, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    physicalCompletedFiniteSource k x=nativeSourceProjectiveBoundaryJetSynthesis 2 k
      (eulerToNewton (radialFourSourceStep k) (sourceBoundary k x)) := by
  rw [← source_euler_newton_exact k x hF hP]
  exact physical_source_newton k x hx

/-- Full complex polarized transport; all nine Green field crossings remain. -/
theorem physical_pair_newton (eta : ℝ) (h0 : 0<eta) (h1 : eta<1)
    (k : ℕ) (x y : ℕ →₀ ℂ)
    (hx : x.support ⊆ Finset.range 4) (hy : y.support ⊆ Finset.range 4) :
    crossGreenPair eta h0 h1 k k x y=canonicalCompletedNativeProjectiveChiralForm
      (nativeSourceProjectiveBoundaryJetSynthesis 2 k (fourNewtonCoordinates k (fun r : Fin 4 => x r)))
      (nativeSourceProjectiveBoundaryJetSynthesis 2 k (fourNewtonCoordinates k (fun r : Fin 4 => y r))) := by
  rw [cross_green_eq_original]
  unfold crossSignedPair
  rw [physical_source_newton k x hx,physical_source_newton k y hy]

/-- Constant native jet coordinates, determined by the source phases. -/
def criticalJet (a : ℝ) : Fin 4 → ℂ := ![0,-(a:ℂ),0,-1]

theorem critical_newton_coordinates (a : ℝ) (k : ℕ) :
    fourNewtonCoordinates k (fun r : Fin 4 => criticalOddSource a k r)=criticalJet a := by
  have hk : (k:ℂ)+1≠0 := by exact_mod_cast (by positivity : (k:ℝ)+1≠0)
  funext m
  fin_cases m <;> norm_num [fourNewtonCoordinates,critical_coefficient_formula,
    nativeSourceJetOrderPhase,canonicalCompletedC3RadialSecondStep,canonicalGreenJetStep,
    criticalJet,Fin.sum_univ_succ] <;> field_simp [hk] <;> ring_nf <;> norm_num [Complex.I_sq]
  field_simp [show (1:ℂ)+(k:ℂ)≠0 by simpa only [add_comm] using hk]
  ring

theorem critical_source_fixed_jet (a : ℝ) (k : ℕ) :
    physicalCompletedFiniteSource k (criticalOddSource a k)=
      nativeSourceProjectiveBoundaryJetSynthesis 2 k (criticalJet a) := by
  rw [physical_source_newton k _ (critical_four_support a k),critical_newton_coordinates]

theorem critical_jet_from_euler (a : ℝ) (k : ℕ)
    (hF : ∀ i : Fin 4, completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i)≠0)
    (hP : ∀ i : Fin 4, completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i)≠0) :
    eulerToNewton (radialFourSourceStep k) (criticalBoundary a k)=criticalJet a := by
  change eulerToNewton (radialFourSourceStep k) (sourceBoundary k (criticalOddSource a k))=_
  rw [← source_euler_newton_exact k _ hF hP,critical_newton_coordinates]

theorem critical_pair_fixed_jet (eta : ℝ) (h0 : 0<eta) (h1 : eta<1) (k : ℕ) (a b : ℝ) :
    crossGreenPair eta h0 h1 k k (criticalOddSource a k) (criticalOddSource b k)=
      canonicalCompletedNativeProjectiveChiralForm
        (nativeSourceProjectiveBoundaryJetSynthesis 2 k (criticalJet a))
        (nativeSourceProjectiveBoundaryJetSynthesis 2 k (criticalJet b)) := by
  rw [cross_green_eq_original]
  unfold crossSignedPair
  rw [critical_source_fixed_jet a k,critical_source_fixed_jet b k]

end
end CarryEulerNewton
