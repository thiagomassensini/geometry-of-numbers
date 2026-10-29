import TenCriticalTransfer

namespace CarryDirectAnchor
open CarrySelfAdjointOperator CarryCriticalTfvd CarryOddEnergy CarrySummableRadial
open CarryBoundaryReconstruction Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- A concrete expression in the original critical-source budget. It is an
exact real ceiling, not a claim that arbitrary real data are computationally
represented by the Lean kernel. -/
def tenCriticalBudget : ℝ := familyConstant (Finset.range 5) (coefficientFromFin (criticalFin 4))

def tenCriticalCutoff : ℕ := max tenAnchorIndex (Nat.ceil ((tenCriticalBudget+1)*(10:ℝ)^31))

theorem ten_critical_budget_small_of_cutoff (k : ℕ) (hk : tenCriticalCutoff ≤ k) :
    physicalFiniteError 5 (criticalFin 4) k < 1/(10:ℝ)^30 := by
  have hbase : tenAnchorIndex ≤ k := (le_max_left _ _).trans hk
  have hn : Nat.ceil ((tenCriticalBudget+1)*(10:ℝ)^31) ≤ k := (le_max_right _ _).trans hk
  have hnR : (Nat.ceil ((tenCriticalBudget+1)*(10:ℝ)^31):ℝ) ≤ (k:ℝ) := by exact_mod_cast hn
  have hc := Nat.le_ceil ((tenCriticalBudget+1)*(10:ℝ)^31)
  have hsize : (tenCriticalBudget+1)*(10:ℝ)^31 ≤ (k:ℝ) := hc.trans hnR
  have hb : 0≤tenCriticalBudget := family_constant_nonneg _ _
  have hp : (0:ℝ)<(k:ℝ)+1 := by positivity
  have hdiv : tenCriticalBudget/((k:ℝ)+1) < 1/(10:ℝ)^30 := by
    apply (div_lt_iff₀ hp).mpr
    norm_num at hsize ⊢
    nlinarith
  have hstep := ten_step_after_anchor k hbase
  have hpos := radial_step_positive k
  have hs : radialFourSourceStep k ≤ 1 := by
    exact hstep.trans (by norm_num)
  have hs2 : (radialFourSourceStep k)^2 ≤ radialFourSourceStep k := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hs2 hb
  have hdiv' : tenCriticalBudget*radialFourSourceStep k < 1/(10:ℝ)^30 := by
    simpa [radialFourSourceStep,div_eq_mul_inv] using hdiv
  unfold physicalFiniteError tenCriticalBudget at *
  nlinarith

/-- The critical-direction finite source dominates its tail at every step
from this explicit source-dependent index. -/
theorem ten_critical_anchor_at_explicit_cutoff (k : ℕ) (hk : tenCriticalCutoff ≤ k) :
    physicalFiniteError 5 (criticalFin 4) k < finiteSourceEnergy 5 (criticalFin 4) k := by
  exact ten_critical_anchor_of_small k ((le_max_left _ _).trans hk)
    (ten_critical_budget_small_of_cutoff k hk)

end
end CarryDirectAnchor
