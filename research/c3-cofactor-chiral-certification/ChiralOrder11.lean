import CompletedHeadEight
import RelativeDeficit

namespace C3CofactorChiral

open CarryCriticalRelative CarryCriticalSource CarrySelfAdjointOperator
open CarryOddHeadSource
open Filter Topology

noncomputable section
set_option autoImplicit false

/-- The existing source balance theorem specialized to the third odd block.
The original completed C3 head independently supplies invertibility of the old
2×2 prefix; no third-pivot sign is used. -/
theorem odd_third_prefix_isUnit_from_completed_c3 :
    IsUnit (sourceMomentMatrix h 1 2) := by
  simpa [CarryCriticalSource.h, CarrySourceBezout.nativeH] using
    CarryOddHeadSource.odd_prefix_isUnit_from_completed_c3

theorem odd_third_critical_balance_tendsto :
    Tendsto (criticalBalance 1 2) atTop
      (nhds (2 * sourceMomentSchur h 1 2)) := by
  exact critical_balance_tendsto_of_isUnit 1 2
    odd_third_prefix_isUnit_from_completed_c3

/-- The chiral deficit has the canonical order-11 scale. The prefix source
identity is available independently; the limit coefficient may still have
either sign until the third-pivot margin is certified. -/
theorem odd_third_scaled_relative_deficit_tendsto :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ 11 * relativeDeficit 1 2 k)
      atTop (nhds (criticalGapCoefficient 1 2)) := by
  simpa [criticalOrder, physicalGrowth] using
    (critical_scaled_relative_deficit 1 2
      odd_third_prefix_isUnit_from_completed_c3)

theorem odd_third_gap_coefficient_pos_iff :
    0 < criticalGapCoefficient 1 2 ↔ 0 < sourceMomentSchur h 1 2 := by
  exact critical_gap_coefficient_pos_iff 1 2

/-- Eventual strict relative deficit follows only after an independent
strictly-positive source pivot has been supplied. -/
theorem odd_third_relative_deficit_eventually_pos
    (hP : 0 < sourceMomentSchur h 1 2) :
    ∀ᶠ k : ℕ in atTop, 0 < relativeDeficit 1 2 k := by
  have hc : 0 < criticalGapCoefficient 1 2 := odd_third_gap_coefficient_pos_iff.mpr hP
  have ht := odd_third_scaled_relative_deficit_tendsto
  have heventually := (tendsto_order.mp ht).1 0 hc
  filter_upwards [heventually] with k hk
  have hg : 0 < ((k : ℝ) + 1) ^ 11 := by positivity
  exact (mul_pos_iff_of_pos_left hg).mp hk

#print axioms odd_third_critical_balance_tendsto
#print axioms odd_third_prefix_isUnit_from_completed_c3
#print axioms odd_third_scaled_relative_deficit_tendsto
#print axioms odd_third_gap_coefficient_pos_iff
#print axioms odd_third_relative_deficit_eventually_pos

end
end C3CofactorChiral
