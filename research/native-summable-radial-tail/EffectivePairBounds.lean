import EffectiveOddPair

namespace CarrySummableRadial
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy CarryOddCauchy
open CarryEffectiveRadial CarryAllOrderTail CarryMovingRadial NativeLaguerre
open Filter Topology
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Finite, explicit coefficient budget for one ORIGINAL ordered Cauchy
filter, at its actual material addresses. -/
def oddFilterBudget (r s p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (2*s+2), ‖(oddFilterCoefficient r s j:ℂ)‖ * ((j+1:ℕ):ℝ)^p

theorem odd_filter_budget_nonneg (r s p : ℕ) : 0 ≤ oddFilterBudget r s p := by
  unfold oddFilterBudget
  positivity

theorem odd_filter_effective_tail_bound (M r s : ℕ) (z : ℂ)
    (hz : ∀ j < 2*s+2, ‖((j+1:ℕ):ℂ)*z‖ < 1) :
    ‖oddFilter r s (effectiveRemainderSamples M z)‖ ≤
      oddFilterBudget r s (2*M+1)/2 := by
  unfold oddFilter
  calc
    _ ≤ ∑ j ∈ Finset.range (2*s+2),
        ‖(oddFilterCoefficient r s j:ℂ)*effectiveRemainderSamples M z j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (2*s+2),
        (‖(oddFilterCoefficient r s j:ℂ)‖ * ((j+1:ℕ):ℝ)^(2*M+1))/2 := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := effective_remainder_norm M (((j+1:ℕ):ℂ)*z)
        (hz j (Finset.mem_range.mp hj))
      unfold effectiveRemainderSamples monomialWeight
      simp only [norm_mul, norm_pow, norm_natCast]
      have hp : 0 ≤ ‖(oddFilterCoefficient r s j:ℂ)‖ * ((j+1:ℕ):ℝ)^(2*M+1) := by positivity
      have hm := mul_le_mul_of_nonneg_left hb hp
      nlinarith
    _ = _ := by simp [oddFilterBudget, Finset.sum_div]

theorem odd_pair_effective_tail_bound (M r s : ℕ) (z : ℂ)
    (hz : ∀ j < 2*max r s+2, ‖((j+1:ℕ):ℂ)*z‖ < 1) :
    ‖oddPairKernel (effectiveRemainderSamples M z) r s‖ ≤
      (oddFilterBudget r s (2*M+1)+oddFilterBudget s r (2*M+1))/2 := by
  rw [native_odd_ordered_filters]
  have ha := odd_filter_effective_tail_bound M r s z (fun j hj => hz j (by
    have := le_max_right r s; omega))
  have hb := odd_filter_effective_tail_bound M s r z (fun j hj => hz j (by
    have := le_max_left r s; omega))
  exact (norm_add_le _ _).trans (by linarith)

/-- Actual derivative of one ordered filter, with the moving original
material address and the factorial Cauchy coefficient retained. -/
def oddFilterTailDerivative (M r s : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (2*s+2), (oddFilterCoefficient r s j:ℂ) *
    ((j+1:ℕ):ℂ)^(2*M+1) *
    (deriv (effectiveResponseRemainder M) (((j+1:ℕ):ℂ)*z)*((j+1:ℕ):ℂ))

theorem odd_filter_tail_hasDerivAt (M r s : ℕ) (z : ℂ)
    (hz : ∀ j < 2*s+2, ‖((j+1:ℕ):ℂ)*z‖ < 1) :
    HasDerivAt (fun w => oddFilter r s (effectiveRemainderSamples M w))
      (oddFilterTailDerivative M r s z) z := by
  unfold oddFilter oddFilterTailDerivative
  apply HasDerivAt.fun_sum
  intro j hj
  have ha := (effective_remainder_analytic M (((j+1:ℕ):ℂ)*z)
    (hz j (Finset.mem_range.mp hj))).differentiableAt.hasDerivAt
  have hi : HasDerivAt (fun w : ℂ => ((j+1:ℕ):ℂ)*w) ((j+1:ℕ):ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul ((j+1:ℕ):ℂ)
  have hd := ha.comp z hi
  simpa only [effectiveRemainderSamples,monomialWeight,mul_assoc,Function.comp_def] using
    hd.const_mul ((oddFilterCoefficient r s j:ℂ)*((j+1:ℕ):ℂ)^(2*M+1))

theorem odd_filter_tail_derivative_bound (M r s : ℕ) (z : ℂ)
    (hz : ∀ j < 2*s+2, ‖((j+1:ℕ):ℂ)*z‖ ≤ 1/4) :
    ‖oddFilterTailDerivative M r s z‖ ≤ 2*oddFilterBudget r s (2*M+2) := by
  unfold oddFilterTailDerivative
  calc
    _ ≤ ∑ j ∈ Finset.range (2*s+2), ‖(oddFilterCoefficient r s j:ℂ) *
        ((j+1:ℕ):ℂ)^(2*M+1) *
        (deriv (effectiveResponseRemainder M) (((j+1:ℕ):ℂ)*z)*((j+1:ℕ):ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (2*s+2),
        2*(‖(oddFilterCoefficient r s j:ℂ)‖ * ((j+1:ℕ):ℝ)^(2*M+2)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hb := effective_remainder_deriv_bound M (((j+1:ℕ):ℂ)*z)
        (hz j (Finset.mem_range.mp hj))
      simp only [norm_mul,norm_pow,norm_natCast]
      rw [show 2*M+2=(2*M+1)+1 by omega, pow_succ]
      have hp : 0 ≤ ‖(oddFilterCoefficient r s j:ℂ)‖ * ((j+1:ℕ):ℝ)^(2*M+1) * ((j+1:ℕ):ℝ) := by positivity
      have hm := mul_le_mul_of_nonneg_left hb hp
      simp only [pow_succ] at *
      nlinarith
    _ = _ := by simp [oddFilterBudget, Finset.mul_sum]

def oddPairTailDerivative (M r s : ℕ) (z : ℂ) : ℂ :=
  oddFilterTailDerivative M r s z+oddFilterTailDerivative M s r z

theorem odd_pair_tail_hasDerivAt (M r s : ℕ) (z : ℂ)
    (hz : ∀ j < 2*max r s+2, ‖((j+1:ℕ):ℂ)*z‖ < 1) :
    HasDerivAt (fun w => oddPairKernel (effectiveRemainderSamples M w) r s)
      (oddPairTailDerivative M r s z) z := by
  have ha := odd_filter_tail_hasDerivAt M r s z (fun j hj => hz j (by
    have := le_max_right r s; omega))
  have hb := odd_filter_tail_hasDerivAt M s r z (fun j hj => hz j (by
    have := le_max_left r s; omega))
  have he : (fun w => oddPairKernel (effectiveRemainderSamples M w) r s) =
      (fun w => oddFilter r s (effectiveRemainderSamples M w) +
        oddFilter s r (effectiveRemainderSamples M w)) := by
    funext w
    exact native_odd_ordered_filters r s _
  rw [he]
  exact ha.add hb

theorem odd_pair_tail_derivative_bound (M r s : ℕ) (z : ℂ)
    (hz : ∀ j < 2*max r s+2, ‖((j+1:ℕ):ℂ)*z‖ ≤ 1/4) :
    ‖oddPairTailDerivative M r s z‖ ≤
      2*(oddFilterBudget r s (2*M+2)+oddFilterBudget s r (2*M+2)) := by
  unfold oddPairTailDerivative
  have ha := odd_filter_tail_derivative_bound M r s z (fun j hj => hz j (by
    have := le_max_right r s; omega))
  have hb := odd_filter_tail_derivative_bound M s r z (fun j hj => hz j (by
    have := le_max_left r s; omega))
  exact (norm_add_le _ _).trans (by linarith)

end
end CarrySummableRadial
