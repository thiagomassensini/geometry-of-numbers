import UniformCutoff

namespace CarrySourceTail
open CarrySelfAdjointOperator CarryCriticalSource
open scoped Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem cutoffError_pos (s N : ℕ) : 0 < cutoffError s N := by
  unfold cutoffError
  exact div_pos (mul_pos (pow_pos rate_pos _) (add_pos (pow_pos rate_pos _) (pow_pos rate_pos _)))
    denominator_pos

/-- Uniform in the number of remaining columns AND in every input. The
cutoff changes here; positivity of those changing prefixes is NOT supplied. -/
theorem uniform_cutoff_accuracy (s : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (M : ℕ) (x : Fin N → ℂ) (a : Fin M → ℂ),
      ‖sourcePair s (Fin.append x a) (Fin.append x a)-sourcePair s x x‖ ≤
        ε*(coefficientEnergy x+coefficientEnergy a) := by
  filter_upwards [(tendsto_order.mp (cutoffError_tendsto_zero s)).2 ε hε] with N hN
  intro M x a
  exact (sourcePair_diagonal_cutoff_bound s x a).trans
    (mul_le_mul_of_nonneg_right hN.le
      (add_nonneg (coefficientEnergy_nonneg x) (coefficientEnergy_nonneg a)))

/-- Limitation of THIS absolute envelope: already after two columns its
budget exceeds the last native diagonal of the retained prefix. This is
not a negative source direction and is not a no-go for relative estimates. -/
theorem cutoff_budget_exceeds_last_native_diagonal (s n : ℕ) :
    h (2*(n+1)+s) < cutoffError s (n+2) := by
  have hb : h (2*(n+1)+s) ≤ rate^(2*(n+1)+s+1) := by
    calc
      _ ≤ |h (2*(n+1)+s)| := le_abs_self _
      _ ≤ rate^(2*(n+1)+s+1)-(1/25:ℝ)^(2*(n+1)+s+1) :=
        canonicalCompletedNativeLogDerivativeMoment_sharp_decay _
      _ ≤ _ := sub_le_self _ (by positivity)
  have hg : rate^(2*(n+1)+s+1) ≤ rate^((s+1)+(n+2)) :=
    pow_le_pow_of_le_one rate_pos.le rate_lt_one.le (by omega)
  apply lt_of_le_of_lt (hb.trans hg)
  rw [cutoffError, pow_add, lt_div_iff₀ denominator_pos]
  have hc := pow_pos rate_pos (s+1)
  have hn := pow_pos rate_pos (n+2)
  have ht := pow_pos rate_pos (2*(n+2))
  have hr := sq_nonneg rate
  nlinarith [mul_nonneg (mul_nonneg hc.le hn.le) hr, mul_pos hc ht]

end
end CarrySourceTail
