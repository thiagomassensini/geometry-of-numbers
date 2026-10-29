import CauchyBeta

namespace CarryCenteredStirling
open CarrySelfAdjointOperator
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def stencilPair (m n d : ℕ) : ℂ :=
  ((m.factorial:ℂ)*(n.factorial:ℂ))⁻¹ *
  ∑ i ∈ Finset.range (m+1), ∑ j ∈ Finset.range (n+1),
    completedGreenForwardWeight m i*completedGreenForwardWeight n j*
      ((((i+1:ℕ):ℂ)^d+((j+1:ℕ):ℂ)^d)/(((i+j+2:ℕ):ℝ):ℂ))

/-- Exact source-origin reduction of both ordered Cauchy legs to two finite
factorial sums. Both indices remain arbitrary and independent. -/
theorem stencil_pair_physical_reduction (m n d : ℕ) :
    stencilPair m n d =
      ((-1:ℂ)^n/(m.factorial:ℂ))*
        (∑ i ∈ Finset.range (m+1), completedGreenForwardWeight m i *
          (((i+1:ℕ):ℂ)^d)*((i+1).factorial:ℂ)/((i+n+2).factorial:ℂ)) +
      ((-1:ℂ)^m/(n.factorial:ℂ))*
        (∑ j ∈ Finset.range (n+1), completedGreenForwardWeight n j *
          (((j+1:ℕ):ℂ)^d)*((j+1).factorial:ℂ)/((j+m+2).factorial:ℂ)) := by
  have he (i j : ℕ) :
      completedGreenForwardWeight m i*completedGreenForwardWeight n j*
        ((((i+1:ℕ):ℂ)^d+((j+1:ℕ):ℂ)^d)/(((i+j+2:ℕ):ℝ):ℂ)) =
      completedGreenForwardWeight m i*(((i+1:ℕ):ℂ)^d)*
        (completedGreenForwardWeight n j / (((i+j+2:ℕ):ℝ):ℂ)) +
      completedGreenForwardWeight n j*(((j+1:ℕ):ℂ)^d)*
        (completedGreenForwardWeight m i / (((j+i+2:ℕ):ℝ):ℂ)) := by
    have ha : j+i+2=i+j+2 := by omega
    rw [ha]
    ring
  unfold stencilPair
  simp_rw [he,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [Finset.sum_comm (s:=Finset.range (m+1)) (t:=Finset.range (n+1))]
  simp_rw [← Finset.mul_sum,physical_stencil_cauchy_beta]
  have hm : (m.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hn : (n.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [mul_add]
  simp_rw [Finset.mul_sum]
  apply congrArg₂ (· + ·)
  all_goals
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hm,hn]

end
end CarryCenteredStirling
