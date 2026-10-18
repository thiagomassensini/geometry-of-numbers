import VariationalSchur

/-! Exact centered evaluation of a logarithmic-derivative recurrence.
The reference coefficients are arbitrary, not alternative source inputs.
The nonlinear remainder is retained; no positivity is assumed. -/
namespace CarryCenteredRecurrence
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem centered_recurrence_identity
    (c C m H L : ℕ → ℝ) (n : ℕ)
    (hm : c 0*m n = -((n+1:ℕ):ℝ)*c (n+1)-
      ∑ k ∈ Finset.range n, m k*c (n-k))
    (hH : C 0*H n = -((n+1:ℕ):ℝ)*C (n+1)-
      ∑ k ∈ Finset.range n, H k*C (n-k))
    (hL : C 0*L n = -((n+1:ℕ):ℝ)*(c (n+1)-C (n+1))-
      (∑ k ∈ Finset.range n, L k*C (n-k))-
      ∑ k ∈ Finset.range (n+1), H k*(c (n-k)-C (n-k))) :
    c 0*(m n-H n-L n) =
      -(∑ k ∈ Finset.range n, (m k-H k-L k)*c (n-k))-
        ∑ k ∈ Finset.range (n+1), L k*(c (n-k)-C (n-k)) := by
  rw [Finset.sum_range_succ,Nat.sub_self] at hL ⊢
  simp only [sub_mul,mul_sub,Finset.sum_sub_distrib] at hL ⊢
  linear_combination hm-hH-hL

end
end CarryCenteredRecurrence
