import LiteralCompanion
import LiteralBudgetLimit

namespace CarrySourceBezout
open CarrySelfAdjointOperator NativeTrace CPFormal.Analytic.Cp
open Filter Topology
noncomputable section
set_option maxHeartbeats 1600000

/-- Factorials fix the exact normalization of the retained derivative channel. -/
theorem sourceJet_neg_deriv (f : ℂ → ℂ) (r : ℕ) :
    sourceJet r (fun w => -deriv f w) = -((r+1:ℕ):ℂ)*sourceJet (r+1) f := by
  unfold sourceJet
  rw [iteratedDeriv_fun_neg, ← iteratedDeriv_succ']
  rw [Nat.factorial_succ]
  push_cast
  have hf : (r.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hr : ((r:ℂ)+1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  field_simp

theorem literal_head_companion_eventually (M : ℕ) :
    (fun w => (headTrace M w).2) =ᶠ[nhds (0:ℂ)]
      (fun w => -deriv (fun z => (headTrace M z).1) w) := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1/2)] with w hw
  have hn : ‖w‖ < (1/2:ℝ) := by simpa using hw
  have hi := Complex.abs_im_le_norm w
  apply literal_head_companion
  norm_num [genuineCriticalStrip,operatorHeightParameter,Complex.mul_re]
  constructor <;> linarith [le_abs_self w.im,neg_abs_le w.im]

theorem literal_tail_companion_eventually (M : ℕ) :
    (fun w => (tailTrace M w).2) =ᶠ[nhds (0:ℂ)]
      (fun w => -deriv (fun z => (tailTrace M z).1) w) := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1/2)] with w hw
  have hn : ‖w‖ < (1/2:ℝ) := by simpa using hw
  have hi := Complex.abs_im_le_norm w
  apply literal_tail_companion
  norm_num [genuineCriticalStrip,operatorHeightParameter,Complex.mul_re]
  constructor <;> linarith [le_abs_self w.im,neg_abs_le w.im]

theorem literal_head_companion_jet (M r : ℕ) :
    sourceJet r (fun w => (headTrace M w).2) =
      -((r+1:ℕ):ℂ)*sourceJet (r+1) (fun w => (headTrace M w).1) := by
  calc
    _ = sourceJet r (fun w => -deriv (fun z => (headTrace M z).1) w) := by
      unfold sourceJet
      rw [(literal_head_companion_eventually M).iteratedDeriv_eq]
    _ = _ := sourceJet_neg_deriv _ r

theorem literal_tail_companion_jet (M r : ℕ) :
    sourceJet r (fun w => (tailTrace M w).2) =
      -((r+1:ℕ):ℂ)*sourceJet (r+1) (fun w => (tailTrace M w).1) := by
  calc
    _ = sourceJet r (fun w => -deriv (fun z => (tailTrace M z).1) w) := by
      unfold sourceJet
      rw [(literal_tail_companion_eventually M).iteratedDeriv_eq]
    _ = _ := sourceJet_neg_deriv _ r

/-- No evenness is assumed for the finite head. The odd companion jet is kept. -/
theorem literal_head_response_odd (M n : ℕ) :
    responseCoefficient (literalHead M) true n =
      (1/2:ℂ)*sourceJet (2*n+1) (fun w => (headTrace M w).2) := by
  rw [responseCoefficient_odd, literal_head_companion_jet]
  simp only [literalHead, show 2*n+1+1=2*(n+1) by omega]
  push_cast
  ring

theorem literal_tail_response_odd (M n : ℕ) :
    responseCoefficient (literalTail M) true n =
      (1/2:ℂ)*sourceJet (2*n+1) (fun w => (tailTrace M w).2) := by
  rw [responseCoefficient_odd, literal_tail_companion_jet]
  simp only [literalTail, show 2*n+1+1=2*(n+1) by omega]
  push_cast
  ring

theorem literal_head_response_even_succ (M n : ℕ) :
    responseCoefficient (literalHead M) false (n+1) =
      (1/2:ℂ)*sourceJet (2*n+1) (fun w => (headTrace M w).2) := by
  rw [responseCoefficient_even_succ, ← literal_head_response_odd, responseCoefficient_odd]

theorem literal_tail_response_even_succ (M n : ℕ) :
    responseCoefficient (literalTail M) false (n+1) =
      (1/2:ℂ)*sourceJet (2*n+1) (fun w => (tailTrace M w).2) := by
  rw [responseCoefficient_even_succ, ← literal_tail_response_odd, responseCoefficient_odd]

end
end CarrySourceBezout
