import C3TailNativeCrosswalkAny

/-!
Fully Lean-certified rational boxes at original C3 cutoff 384 for selected
even height jets, using the any-M completion+boundary crosswalk.
These are conservative, *not* the much sharper Arb external boxes.
-/
namespace CarrySourceBezout
noncomputable section

theorem c3_tail384_jet0 :
    ‖literalTail 384 0-originalC3BoundaryJetAny 384 0‖ ≤ (2/10^30:ℝ) := by
  exact (c3_regrouped_tail_any_bound 384 0 (by norm_num)).trans
    (by norm_num [CarryC3Tail.completedC3TailJetEnvelope])

theorem c3_tail384_jet9 :
    ‖literalTail 384 9-originalC3BoundaryJetAny 384 9‖ ≤ (2/10^19:ℝ) := by
  exact (c3_regrouped_tail_any_bound 384 9 (by norm_num)).trans
    (by norm_num [CarryC3Tail.completedC3TailJetEnvelope])

theorem c3_tail384_jet18 :
    ‖literalTail 384 18-originalC3BoundaryJetAny 384 18‖ ≤ (9/10^9:ℝ) := by
  exact (c3_regrouped_tail_any_bound 384 18 (by norm_num)).trans
    (by norm_num [CarryC3Tail.completedC3TailJetEnvelope])

theorem c3_tail384_jet22 :
    ‖literalTail 384 22-originalC3BoundaryJetAny 384 22‖ ≤ (6/10000:ℝ) := by
  exact (c3_regrouped_tail_any_bound 384 22 (by norm_num)).trans
    (by norm_num [CarryC3Tail.completedC3TailJetEnvelope])

end
end CarrySourceBezout
