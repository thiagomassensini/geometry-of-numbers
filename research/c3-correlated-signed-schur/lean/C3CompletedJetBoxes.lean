import FiniteEvaluationError

/-!
Any M>0: explicit rational source-specific bound on EACH completed
C3 accelerated tail jet. The seed and gamma/value multiplier remain
inside the completed jet; no classical zeta values or numerical floats.
-/
namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CarryC3Gamma CPFormal.Analytic.Cp
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1400000

def completedC3TailAt (M : ℕ) (w : ℂ) : ℂ :=
  valueMultiplier w * acceleratedC3Tail M w

def completedC3TailJetEnvelope (M j : ℕ) : ℝ :=
  (96*(Nat.factorial 14:ℝ)/(729*(3*(M:ℝ)-1)^13))*4^(2*j)

theorem completed_c3_tail_jet_bound_general
    (M j : ℕ) (hM : 0 < M) :
    ‖sourceJet (2*j) (completedC3TailAt M)‖ ≤
      completedC3TailJetEnvelope M j := by
  unfold completedC3TailJetEnvelope
  apply cauchy_quarter
  · intro w hw
    exact (value_multiplier_analytic_at w
      (lt_of_le_of_lt hw (by norm_num))).mul
      (accelerated_c3_tail_analytic M w
        (lt_of_le_of_lt hw (by norm_num)))
  · intro w hw
    rw [completedC3TailAt, norm_mul]
    have hh := mul_le_mul
      (c3_value_multiplier_bound w hw)
      (accelerated_c3_tail_bound M hM w (hw.trans (by norm_num)))
      (norm_nonneg _)
      (by norm_num : (0:ℝ) ≤ 96)
    exact hh.trans_eq (by ring)

end
end CarryC3Tail
