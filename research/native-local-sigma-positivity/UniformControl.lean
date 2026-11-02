import LocalPositivity

/-! Synthetic control only: it does not modify or model the native source. -/
namespace CarryLocalPositivityControl
open Filter Topology
noncomputable section
set_option autoImplicit false

def shrinkingFamily (n : ℕ) (d : ℝ) : ℝ := 1 - (((n:ℝ)+1)*d)^2

theorem shrinkingFamily_even (n : ℕ) (d : ℝ) : shrinkingFamily n (-d) = shrinkingFamily n d := by
  unfold shrinkingFamily
  ring

theorem each_order_eventually_positive (n : ℕ) :
    ∀ᶠ d : ℝ in 𝓝 0, 0 < shrinkingFamily n d := by
  have hc : ContinuousAt (shrinkingFamily n) 0 := by
    unfold shrinkingFamily
    fun_prop
  have h0 : 0 < shrinkingFamily n 0 := by simp [shrinkingFamily]
  exact hc (isOpen_Ioi.mem_nhds h0)

theorem no_common_positive_neighborhood :
    ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∃ d : ℝ, 0 < d ∧ d < ε ∧ shrinkingFamily n d < 0 := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (2/ε)
  have hnmul : 2 < (n:ℝ)*ε := (div_lt_iff₀ hε).mp hn
  refine ⟨n,ε/2,by linarith,by linarith,?_⟩
  unfold shrinkingFamily
  have hm : 1 < ((n:ℝ)+1)*(ε/2) := by nlinarith
  nlinarith

#print axioms shrinkingFamily_even
#print axioms each_order_eventually_positive
#print axioms no_common_positive_neighborhood
end
end CarryLocalPositivityControl
