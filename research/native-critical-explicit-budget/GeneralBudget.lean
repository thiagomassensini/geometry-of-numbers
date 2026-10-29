import DirectBound

namespace CarryExplicitBudget
open CarrySelfAdjointOperator CarryDirectAnchor CarrySummableRadial CarryCriticalTfvd CarryOddEnergy CarryBoundaryReconstruction
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- A uniform bound for the COMPLETE ordered-pair budget, for any finite
family. The constants may depend on the family/order. -/
theorem finite_family_budget_bound (S : Finset ℕ) (c : ℕ → ℝ) (L M : ℝ)
    (hL : 0 ≤ L)
    (hc : ∀ r ∈ S, |c r| ≤ L)
    (hp : ∀ r ∈ S, ∀ s ∈ S, pairConstant r s ≤ M) :
    familyConstant S c ≤ (S.card:ℝ)^2 * L^2 * M := by
  unfold familyConstant
  calc
    _ ≤ ∑ r ∈ S, ∑ s ∈ S, L^2*M := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro s hs
      have hm : |c r*c s| ≤ L^2 := by
        rw [abs_mul,pow_two]
        exact mul_le_mul (hc r hr) (hc s hs) (abs_nonneg _) hL
      calc
        _ ≤ L^2*pairConstant r s := mul_le_mul_of_nonneg_right hm (pair_constant_nonneg r s)
        _ ≤ L^2*M := mul_le_mul_of_nonneg_left (hp r hr s hs) (sq_nonneg L)
    _ = _ := by simp; ring

/-- The physical error bound for arbitrary finite jets, with all crossings
retained and order-dependent constants made explicit. -/
theorem finite_family_direct_budget_bound (S : Finset ℕ) (c : ℕ → ℝ) (L M : ℝ)
    (hL : 0 ≤ L)
    (hc : ∀ r ∈ S, |c r| ≤ L)
    (hp : ∀ r ∈ S, ∀ s ∈ S, pairConstant r s ≤ M)
    (k : ℕ) (hk : oddGridCutoff S ≤ k) :
    |fullEnergy k (finiteOddJetSource S c k) - oddCanonicalForm S c| ≤
      (radialFourSourceStep k)^2*((S.card:ℝ)^2 * L^2 * M) := by
  exact (finite_energy_direct_error S c k hk).trans
    (mul_le_mul_of_nonneg_left (finite_family_budget_bound S c L M hL hc hp) (sq_nonneg _))

end
end CarryExplicitBudget
