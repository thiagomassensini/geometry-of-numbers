import C3TailNativeCrosswalkAny
import GroupedSourceBudget

/-!
Certified FINITE VECTOR of all 23 completed C3 tail jets required by the
signed S gate at n = 9 (odd source block size 11).
Unlike the external Arb boxes, these bounds are proved in Lean from
the original completed C3/TFVD tail and its 12-term boundary.
-/
namespace CarrySourceBezout
open scoped BigOperators
noncomputable section

/-- Same original TFVD tail, after exactly removing its original C3
boundary; j indexes the EVEN height-series coefficient 2*j. -/
def originalC3Tail384 (j : Fin 23) : ℂ :=
  literalTail 384 j.val - originalC3BoundaryJetAny 384 j.val

/-- A certified, completely explicit rational bound for every one
of the 23 coefficients, without a 23-premise hypothesis. -/
def originalC3Box384 (j : Fin 23) : ℝ :=
  CarryC3Tail.completedC3TailJetEnvelope 384 j.val

theorem all_twenty_three_c3_bounds (j : Fin 23) :
    ‖originalC3Tail384 j‖ ≤ originalC3Box384 j := by
  exact c3_regrouped_tail_any_bound 384 j.val (by norm_num)

/-- These bounds are nonnegative and usable directly as coefficient
inputs to the signed impulse budget. -/
theorem all_twenty_three_c3_bounds_nonneg (j : Fin 23) :
    0 ≤ originalC3Box384 j := by
  unfold originalC3Box384 CarryC3Tail.completedC3TailJetEnvelope
  positivity

/-- In the true common source, the correlated linear cost admits a
23-coefficient estimate as soon as the coefficient identity has been
established. That identity is proved in the separate impulse expansion. -/
theorem original_c3_linear_23_budget (ell : Fin 23 → ℂ) :
    ‖∑ j : Fin 23, ell j * originalC3Tail384 j‖ ≤
      ∑ j : Fin 23, ‖ell j‖ * originalC3Box384 j := by
  exact joint_linear_coefficient_budget 23 ell originalC3Tail384
    originalC3Box384 all_twenty_three_c3_bounds

end
end CarrySourceBezout
