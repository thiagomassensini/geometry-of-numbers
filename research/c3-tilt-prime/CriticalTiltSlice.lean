import CarrySelfAdjointOperator.CompletedNativeCentralCarryTiltSensitivity
import CarrySelfAdjointOperator.PrimeDepthAllOrderMomentBridge

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

def criticalParameter (t : ℝ) : ℂ := (1/2:ℂ) + Complex.I*(t:ℂ)

theorem criticalParameter_re (t : ℝ) : (criticalParameter t).re = (1/2:ℝ) := by
  simp [criticalParameter]

theorem radial_zero (t : ℝ) : criticalDisplacement (criticalParameter t).re = 0 := by
  simp [criticalDisplacement,criticalParameter_re]

theorem weighted_tilt_zero (k : ℕ) (t : ℝ) :
    canonicalCriticalWeightedTiltBlock k (criticalParameter t) = 0 := by
  unfold canonicalCriticalWeightedTiltBlock
  rw [radial_zero,cpTilt_zero 3 (by norm_num)]
  simp

theorem cross_zero (k : ℕ) (t : ℝ) :
    localCriticalCarrierCross (criticalParameter t) (canonicalRealCpCenter k) 1 = 0 := by
  simp [localCriticalCarrierCross,complexTransversePowerProfile,transversePowerProfile,radial_zero]

theorem curvature_on_line (k : ℕ) (t : ℝ) :
    localCriticalCarrierCurvature (criticalParameter t) (canonicalRealCpCenter k) 1 =
      CPFormal.centeredSecondDifference (localCriticalLineCarrier (criticalParameter t) (canonicalRealCpCenter k)) 0 1 := by
  simp [localCriticalCarrierCurvature,complexTransversePowerProfile,transversePowerProfile,radial_zero]

theorem bracket_line_eq_carrier (k : ℕ) (t : ℝ) :
    realCpSaturatedBracket 3 k (criticalParameter t) =
      CPFormal.centeredSecondDifference (localCriticalLineCarrier (criticalParameter t) (canonicalRealCpCenter k)) 0 1 := by
  rw [realCpSaturatedBracket_three_eq_weightedTilt_add_carrierRemainder,
    weighted_tilt_zero]
  simp only [zero_add,canonicalCriticalCarrierRemainderBlock,cross_zero,add_zero,curvature_on_line]

theorem finite_tilt_zero (M : ℕ) (t : ℝ) :
    finiteCanonicalCriticalWeightedTiltTrace M (criticalParameter t) = 0 := by
  simp [finiteCanonicalCriticalWeightedTiltTrace,weighted_tilt_zero]

theorem finite_tilt_vertical_jets_zero (M n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (criticalParameter u)) t = 0 := by
  have h : (fun u : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (criticalParameter u)) = 0 := by
    funext u
    exact finite_tilt_zero M u
  rw [h]
  exact iteratedDeriv_const_zero

theorem finite_bracket_line (M : ℕ) (t : ℝ) :
    finiteCanonicalBracketTrace M (criticalParameter t) =
      finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter t) := by
  rw [finiteCanonicalBracketTrace_eq_weightedTilt_add_carrierRemainder,finite_tilt_zero,zero_add]

theorem finite_bracket_vertical_jets (M n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun u : ℝ => finiteCanonicalBracketTrace M (criticalParameter u)) t =
      iteratedDeriv n (fun u : ℝ => finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter u)) t := by
  have h : (fun u : ℝ => finiteCanonicalBracketTrace M (criticalParameter u)) =
      (fun u : ℝ => finiteCanonicalCriticalCarrierRemainderTrace M (criticalParameter u)) := by
    funext u
    exact finite_bracket_line M u
  rw [h]

theorem transverse_sensitivity_positive (M : ℕ) (hM : 0 < M) :
    0 < deriv (finiteCanonicalRealCriticalWeightedTiltTrace M) 0 :=
  deriv_finiteCanonicalRealCriticalWeightedTiltTrace_zero_pos hM

#print axioms weighted_tilt_zero
#print axioms cross_zero
#print axioms bracket_line_eq_carrier
#print axioms finite_tilt_vertical_jets_zero
#print axioms finite_bracket_vertical_jets
#print axioms transverse_sensitivity_positive
#print axioms canonicalCompletedNativeLogDerivativeMoment_eq_primeDepthResponse
end
end CarryTiltSlice
