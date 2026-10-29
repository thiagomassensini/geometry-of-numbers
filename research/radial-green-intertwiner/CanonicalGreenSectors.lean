import CompletedTfvdTransport

namespace CarryRadialGreen
open CarryPhysicalTrace CarryRadialRefinement CarrySelfAdjointOperator
open CarrySelfAdjointOperator.NativeLaguerre
open scoped BigOperators ComplexConjugate InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

def reconstructedBulk (m : ℕ) (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) : PhysicalPair :=
  (η : ℂ) • ((pairResolvent (m+1) η)^2) (pairPower m (bulkBoundary η k x))

def reconstructedResidual (m : ℕ) (η : ℝ) (k : ℕ) (x : ℕ →₀ ℂ) : PhysicalPair :=
  (η : ℂ) • ((pairResolvent (m+1) η)^2) (pairPower m (residualNumerator η k x))

def correctedGreenPairing (η : ℝ) (k l i j : ℕ) : ℂ :=
  physicalForm (reconstructedBulk l η k (Finsupp.single i 1))
    (reconstructedBulk k η l (Finsupp.single j 1))+
  physicalForm (reconstructedBulk l η k (Finsupp.single i 1))
    (reconstructedResidual k η l (Finsupp.single j 1))+
  physicalForm (reconstructedResidual l η k (Finsupp.single i 1))
    (reconstructedBulk k η l (Finsupp.single j 1))+
  physicalForm (reconstructedResidual l η k (Finsupp.single i 1))
    (reconstructedResidual k η l (Finsupp.single j 1))

/-- Both vector ports and all four sectors of the ORIGINAL source Green
reconstruction. No coefficient of the target moment sequence defines a state. -/
theorem corrected_green_pairing_is_common (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (k l i j : ℕ) : correctedGreenPairing η k l i j = commonPairing k l i j := by
  have h := refined_completed_four_sectors l k η hη0 hη1 k l
    (Finsupp.single i 1) (Finsupp.single j 1)
  symm
  simpa only [completedSource,Finsupp.linearCombination_single,one_smul,
    commonPairing,physicalForm,reconstructedBulk,reconstructedResidual,correctedGreenPairing] using h

/-- Exact native readout of the WHOLE transported TFVD/Green expression. -/
theorem corrected_green_pairing_is_canonical (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (k l i j : ℕ)
    (hz : operatorHeightParameter (canonicalCompletedC3RadialTiltPoint k i) ∈ CPFormal.Analytic.Cp.genuineCriticalStrip)
    (hzF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hwF : completedNativeOperatorCharacteristic (canonicalCompletedC3RadialTiltPoint l j) ≠ 0)
    (hzP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint k i) ≠ 0)
    (hwP : completedNativePositiveHermiteBiehlerCoordinate (canonicalCompletedC3RadialTiltPoint l j) ≠ 0) :
    correctedGreenPairing η k l i j = canonicalCompletedNativePolarizedDslopeKernel
      (canonicalCompletedC3RadialTiltPoint k i) (canonicalCompletedC3RadialTiltPoint l j) := by
  rw [corrected_green_pairing_is_common η hη0 hη1]
  exact common_pairing_kernel k l i j hz hzF hwF hzP hwP

/-- The auxiliary Green weight cannot manufacture a different total kernel. -/
theorem corrected_green_weight_independent (η ξ : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (k l i j : ℕ) : correctedGreenPairing η k l i j = correctedGreenPairing ξ k l i j := by
  rw [corrected_green_pairing_is_common η hη0 hη1,corrected_green_pairing_is_common ξ hξ0 hξ1]

end
end CarryRadialGreen
