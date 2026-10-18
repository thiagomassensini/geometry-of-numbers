import UniformCutoff

/-! A necessary scale for a source-derived all-order certificate. This is a
statement about the actual source and actual return, not a free-field model. -/
namespace CarrySourceTail
open CarrySelfAdjointOperator CarryCriticalSource
open Filter
open scoped BigOperators Matrix Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem source_pivot_le_diagonal (s n : ℕ)
    (hp : (sourceMomentMatrix h s n).PosDef) :
    sourceMomentSchur h s n ≤ h (2*n+s) := by
  have he := sourceMomentSchur_sewing h s n hp (0:Fin n → ℝ) 1
  have hz : sourceMomentQuadratic h s (n+1) (Fin.snoc (0:Fin n → ℝ) 1) =
      h (2*n+s) := by
    rw [sourceMomentQuadratic_snoc]
    simp [sourceMomentQuadratic]
  rw [hz] at he
  simp only [zero_add, one_smul, one_pow, mul_one] at he
  have hn : 0 ≤ sourceMomentQuadratic h s n
      ((sourceMomentMatrix h s n)⁻¹ *ᵥ sourceMomentCoupling h s n) :=
    hp.posSemidef.dotProduct_mulVec_nonneg _
  linarith

/-- This upper bound uses no sign assumption for the NEW pivot. -/
theorem source_pivot_geometric_upper (s n : ℕ)
    (hp : (sourceMomentMatrix h s n).PosDef) :
    sourceMomentSchur h s n ≤ rate^(2*n+s+1) := by
  calc
    _ ≤ h (2*n+s) := source_pivot_le_diagonal s n hp
    _ ≤ |h (2*n+s)| := le_abs_self _
    _ ≤ rate^(2*n+s+1)-(1/25:ℝ)^(2*n+s+1) :=
      canonicalCompletedNativeLogDerivativeMoment_sharp_decay _
    _ ≤ _ := sub_le_self _ (by positivity)

/-- A positive lower margin for the actual incident-minus-return balance
must shrink with order; the source clock and all Jordan crossings remain. -/
theorem physical_critical_margin_upper (s : Fin 2) (n : ℕ)
    (hp : (sourceMomentMatrix h s.val n).PosDef) (ε : ℝ)
    (hb : ∀ᶠ k : ℕ in atTop, ε ≤ criticalBalance s n k) :
    ε ≤ 2*rate^(2*n+s.val+1) := by
  have hl := ge_of_tendsto (criticalBalance_tendsto s n hp) hb
  linarith [source_pivot_geometric_upper s.val n hp]

/-- No FIXED positive raw margin can certify every step, even if positivity
itself is true at all orders. This does not exclude order-dependent margins. -/
theorem no_fixed_physical_critical_margin (s : Fin 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, (sourceMomentMatrix h s.val n).PosDef →
      ¬ (∀ᶠ k : ℕ in atTop, ε ≤ criticalBalance s n k) := by
  have ht : Tendsto (fun n : ℕ => 2*rate^(n+1)) atTop (nhds 0) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one rate_pos.le rate_lt_one).mul_const
      rate).const_mul (2:ℝ)
    simpa only [pow_succ, zero_mul, mul_zero] using hh
  obtain ⟨n,hn⟩ := ((tendsto_order.mp ht).2 ε hε).exists
  refine ⟨n,fun hp hb => ?_⟩
  have hu := physical_critical_margin_upper s n hp ε hb
  have hg : rate^(2*n+s.val+1) ≤ rate^(n+1) :=
    pow_le_pow_of_le_one rate_pos.le rate_lt_one.le (by omega)
  linarith

end
end CarrySourceTail
