import ExplicitBudgets

namespace CarryReadoutBounds
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryFourthTail CarrySelfAdjointOperator NativeMomentOrthogonalization
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem response_constants_odd : explicitResponseConstant 1=163872 ∧
    explicitResponseConstant 3=11141952 ∧ explicitResponseConstant 5=715668480 := by
  norm_num [explicitResponseConstant, Finset.sum_range_succ]

/-- An error certificate, not a sign certificate. The coefficient bound is explicit. -/
theorem second_even_error_at_100000 (a : ℝ) (ha : |a| ≤ 1/100) :
    |secondEvenResidual a-secondEvenObservation a 100000| < 1/50000000 := by
  have hb := second_even_residual_error a 100000 (by norm_num)
  obtain ⟨h1,h3,h5⟩ := response_constants_odd
  rw [h1,h3,h5] at hb
  have hs : a^2 ≤ (1/10000:ℝ) := by nlinarith [abs_nonneg a, sq_abs a]
  apply hb.trans_lt
  norm_num
  nlinarith [abs_nonneg a]

/-- All six requested multipliers are covered by the unconditional all-order bounds. -/
theorem first_six_multiplier_bounds (j : Fin 6) :
    ‖rJet j.val ordinaryMultiplier‖ ≤ 8192*8^j.val ∧
    ‖rJet j.val clockMultiplier‖ ≤ (4:ℝ)^j.val :=
  ⟨ordinary_multiplier_jet_bound _, clock_multiplier_jet_bound _⟩

/-- The residual is the original signed PR41 pivot; zero cases are not
misrepresented as invertibility. -/
theorem second_even_residual_eq_pivot :
    secondEvenResidual (canonicalCompletedNativeLogDerivativeMoment 1/canonicalCompletedNativeLogDerivativeMoment 0) =
      carryPairingPivot (hankelPairing canonicalCompletedNativeLogDerivativeMoment) 1 := by
  unfold secondEvenResidual
  simp only [carryPairingPivot, hankelPairing, carryPairingRemainder]
  norm_num
  by_cases hz : canonicalCompletedNativeLogDerivativeMoment 0=0
  · simp [hz]
  · field_simp
    ring

theorem second_even_critical_error_at_100000
    (ha : |canonicalCompletedNativeLogDerivativeMoment 1/canonicalCompletedNativeLogDerivativeMoment 0| ≤ 1/100) :
    |carryPairingPivot (hankelPairing canonicalCompletedNativeLogDerivativeMoment) 1-
      secondEvenObservation (canonicalCompletedNativeLogDerivativeMoment 1/canonicalCompletedNativeLogDerivativeMoment 0) 100000|
      < 1/50000000 := by
  rw [← second_even_residual_eq_pivot]
  exact second_even_error_at_100000 _ ha

end
end CarryReadoutBounds
