import MomentKernelJets

namespace CarryCompletedPairing
open CarryCameraTail CarryMaterialTheta CarryFourLeg CarryGreenProvenance
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
open scoped ComplexConjugate BigOperators
noncomputable section
set_option autoImplicit false

theorem value_gain_ne_zero {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) : valueGain z ≠ 0 := by
  exact div_ne_zero (nativeXiCompletionFactor_ne_zero hz)
    (cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hz)

/-- Completion cannot repair unequal material value coordinates by merely
identifying them. This does not assert a global C2--C3 stitching map. -/
theorem completion_preserves_value_distinction {z : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip) (p q : ℂ × ℂ)
    (hpq : p.1 ≠ q.1) : (nativeCompletionTrace z p).1 ≠ (nativeCompletionTrace z q).1 := by
  rw [native_completion_matrix, native_completion_matrix]
  exact fun h => hpq (mul_left_cancel₀ (value_gain_ne_zero hz) h)

/-- An exact control on the COMPLETION MAP, on independent value/log-jet
coordinates. These basis probes are not asserted to be whole physical
source states. The extra term is forced by the original height factor. -/
theorem completion_basis_defect (z w : ℂ) :
    mixedScalarBoundaryWedge
        (nativeCompletionTrace z (1,0)).1 (nativeCompletionTrace z (1,0)).2
        (nativeCompletionTrace w (0,1)).1 (nativeCompletionTrace w (0,1)).2 -
      jetGain z * conj (valueGain w) * mixedScalarBoundaryWedge 1 0 0 1 =
        2 * Complex.I * valueGain z * conj (valueGain w) := by
  rw [native_completion_pairing, CompletionPairingChannels.total,
    completion_jet_transport_exact]
  simp only [completionPairingChannels, map_zero, mul_zero, mul_one, map_one, add_zero]
  ring

theorem completion_basis_defect_ne_zero {z w : ℂ}
    (hz : operatorHeightParameter z ∈ genuineCriticalStrip)
    (hw : operatorHeightParameter w ∈ genuineCriticalStrip) :
    mixedScalarBoundaryWedge
        (nativeCompletionTrace z (1,0)).1 (nativeCompletionTrace z (1,0)).2
        (nativeCompletionTrace w (0,1)).1 (nativeCompletionTrace w (0,1)).2 -
      jetGain z * conj (valueGain w) * mixedScalarBoundaryWedge 1 0 0 1 ≠ 0 := by
  rw [completion_basis_defect]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (value_gain_ne_zero hz))
    (by simpa using value_gain_ne_zero hw)

/-- Exact change in the readout residual when the two target log jets are
rotated to height companions. The local legs, both overlap roles and all
ordered crosses remain fixed throughout the comparison. -/
theorem height_readout_defect {ι : Type*} [Fintype ι]
    (a b c d : ℂ) (legs : ReflectedBoundarySynthesisData ι) :
    mixedBoundaryResidualCorrection a (Complex.I*b) c (Complex.I*d) legs -
      mixedBoundaryResidualCorrection a b c d legs =
        (Complex.I-1)*b*conj c + (Complex.I+1)*a*conj d := by
  have hi := mixedScalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection
    a (Complex.I*b) c (Complex.I*d) legs
  have hb := mixedScalarBoundaryWedge_eq_localTwoLeg_add_cross_add_residualCorrection
    a b c d legs
  simp only [mixedScalarBoundaryWedge, map_mul, Complex.conj_I] at hi hb
  linear_combination hb - hi

theorem integral_height_readout_defect (M : ℕ) (z w : ℂ) :
    let p := materialHeadTrace M (operatorHeightParameter z)
    let q := materialHeadTrace M (operatorHeightParameter w)
    integralHeightReadout M z w -
      heatReadoutCorrection M (operatorHeightParameter z) (operatorHeightParameter w) =
        (Complex.I-1)*p.2*conj q.1 + (Complex.I+1)*p.1*conj q.2 := by
  exact height_readout_defect _ _ _ _ _

end
end CarryCompletedPairing
