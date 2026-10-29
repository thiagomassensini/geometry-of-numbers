import AcceleratedGreen

/-! Exact rational precision regressions on the INFINITE native jet tails.
These are error certificates, not moment/pivot positivity certificates. -/
namespace CarryFourthTail
open GeometryOfNumbers.Analysis CarryCellTail
noncomputable section
set_option autoImplicit false

theorem ordinary_fifth_501_error_lt :
    ‖rJet 5 (acceleratedOrdinaryTail 501)‖ < (1/100000000:ℝ) := by
  apply lt_of_le_of_lt (accelerated_ordinary_jet_bound 5 501 (by norm_num))
  norm_num [acceleratedOrdinaryBudget]

theorem clock_fifth_1145_error_lt :
    ‖rJet 5 (acceleratedClockTail 1145)‖ < (1/100000000:ℝ) := by
  apply lt_of_le_of_lt (accelerated_clock_jet_bound 5 1145 (by norm_num))
  norm_num [acceleratedClockBudget]

theorem critical_budget_gain_at_16 (s : Fin 2) (n : ℕ) :
    5*criticalErrorConstant s n/(4*(4*(16:ℝ)-1)^3) =
      (5/3969:ℝ)*criticalErrorBudget s n 16 := by
  convert critical_budget_improvement s n 16 (by norm_num) using 1 <;> norm_num
end
end CarryFourthTail
