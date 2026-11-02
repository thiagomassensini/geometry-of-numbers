import SwapCapstone
import FiniteEvaluationError

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def infiniteCarrierRemainder (t d : ℝ) : ℂ :=
  ∑' k : ℕ, canonicalCriticalCarrierRemainderBlock k (displacedParameter d t)

theorem infiniteCarrierRemainder_summable (t d : ℝ) (hdlo : -(1/4:ℝ) < d)
    (hdhi : d < 1/4) :
    Summable (fun k : ℕ => canonicalCriticalCarrierRemainderBlock k (displacedParameter d t)) := by
  have hs : -1 < (displacedParameter d t).re := by rw [displacedParameter_re]; linarith
  have hb := summable_realCpSaturatedBracket 3 (by norm_num) hs
  have hw := infiniteTransverseTilt_summable t d hdlo hdhi
  have heq : (fun k : ℕ => canonicalCriticalCarrierRemainderBlock k (displacedParameter d t)) =
      (fun k : ℕ => realCpSaturatedBracket 3 k (displacedParameter d t) -
        canonicalCriticalWeightedTiltBlock k (displacedParameter d t)) := by
    funext k
    rw [realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder]
    ring
  rw [heq]
  exact hb.sub hw

theorem infinite_c3_tilt_carrier_ledger (t d : ℝ) (hdlo : -(1/4:ℝ) < d)
    (hdhi : d < 1/4) :
    bracketedDirichletChart 3 (displacedParameter d t) =
      1 + infiniteTransverseTilt t d + infiniteCarrierRemainder t d := by
  have hw := infiniteTransverseTilt_summable t d hdlo hdhi
  have hr := infiniteCarrierRemainder_summable t d hdlo hdhi
  have heq : (fun k : ℕ => realCpSaturatedBracket 3 k (displacedParameter d t)) =
      (fun k : ℕ => canonicalCriticalWeightedTiltBlock k (displacedParameter d t) +
        canonicalCriticalCarrierRemainderBlock k (displacedParameter d t)) := by
    funext k
    exact realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder k _
  unfold bracketedDirichletChart infiniteTransverseTilt infiniteCarrierRemainder
  rw [seedSum_three_dirichlet_eq_one,heq,hw.tsum_add hr]
  ring

theorem completed_parameter_decomposition (t d : ℝ) (hdlo : -(1/4:ℝ) < d)
    (hdhi : d < 1/4) :
    completedNativeOperatorCharacteristic ((t:ℂ)-Complex.I*(d:ℂ)) =
      CarryTwoEvenJets.valueMultiplier ((t:ℂ)-Complex.I*(d:ℂ)) *
        (1 + infiniteTransverseTilt t d + infiniteCarrierRemainder t d) := by
  have he : operatorHeightParameter ((t:ℂ)-Complex.I*(d:ℂ)) = displacedParameter d t := by
    unfold operatorHeightParameter displacedParameter
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [CarryC3Tail.characteristic_c3_formula]
  change CarryTwoEvenJets.valueMultiplier _ * bracketedDirichletChart 3 _ = _
  rw [he,infinite_c3_tilt_carrier_ledger t d hdlo hdhi]

#print axioms infiniteCarrierRemainder_summable
#print axioms infinite_c3_tilt_carrier_ledger
#print axioms completed_parameter_decomposition
end
end CarryTiltSlice
