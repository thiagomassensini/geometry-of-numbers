import LiteralTailBounds
import LiteralTfvd
import C3CompletedJetBoxes

/-!
For EVERY cutoff M the exact accelerated C3 source tail = literal native
TFVD tail minus the ORIGINAL 12-weight C3 boundary, AFTER completion.
No choice of camera, center, gamma, cutoff or moment normalization changes.
-/
namespace CarrySourceBezout
open CarrySelfAdjointOperator CPFormal.Analytic.Cp NativeTrace
open Filter Topology
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

def originalC3BoundaryJetAny (M j : ℕ) : ℂ :=
  NativeTrace.sourceJet (2*j)
    (fun w => NativeTrace.valueMultiplier w *
      CarryC3Tail.c3Boundary (fun k => CarryC3Tail.c3Sample k w) (3*M+2))

theorem original_c3_boundary_any_analytic (M : ℕ) :
    AnalyticAt ℂ
      (fun w => NativeTrace.valueMultiplier w *
        CarryC3Tail.c3Boundary (fun k => CarryC3Tail.c3Sample k w) (3*M+2)) 0 := by
  exact NativeTrace.valueMultiplier_analytic.mul
    ((CarryC3Tail.c3_boundary_entire (3*M+2) (by omega)).analyticAt 0)

theorem source_regrouped_c3_tail_any (M j : ℕ) :
    literalTail M j - originalC3BoundaryJetAny M j =
      NativeTrace.sourceJet (2*j) (CarryC3Tail.completedC3TailAt M) := by
  unfold originalC3BoundaryJetAny
  simp only [literalTail]
  have hsub := iteratedDeriv_sub (n:=2*j)
    (NativeTrace.tail_value_analytic M).contDiffAt
    (original_c3_boundary_any_analytic M).contDiffAt
  simp only [NativeTrace.sourceJet]
  rw [← sub_div, ← hsub]
  congr 1
  congr 1
  funext w
  dsimp only [Pi.sub_apply]
  rw [literal_tail_value_formula]
  unfold CarryC3Tail.completedC3TailAt CarryC3Tail.acceleratedC3Tail
  change NativeTrace.valueMultiplier w *
      realCpBracketCutoffTail 3 M (operatorHeightParameter w) -
      NativeTrace.valueMultiplier w *
        CarryC3Tail.c3Boundary (fun k => CarryC3Tail.c3Sample k w) (3*M+2) =
        NativeTrace.valueMultiplier w *
          (realCpBracketCutoffTail 3 M (operatorHeightParameter w) -
            CarryC3Tail.c3Boundary (fun k => CarryC3Tail.c3Sample k w) (3*M+2))
  ring

/-- The original source-tail coefficient inherits the all-cutoff rational box.
The EVEN jet indexing 2*j is explicit: no confusion with coefficient j. -/
theorem c3_regrouped_tail_any_bound (M j : ℕ) (hM : 0 < M) :
    ‖literalTail M j - originalC3BoundaryJetAny M j‖ ≤
      CarryC3Tail.completedC3TailJetEnvelope M j := by
  rw [source_regrouped_c3_tail_any]
  exact CarryC3Tail.completed_c3_tail_jet_bound_general M j hM

end
end CarrySourceBezout
