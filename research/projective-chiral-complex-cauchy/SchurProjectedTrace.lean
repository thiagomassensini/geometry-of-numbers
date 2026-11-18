import PhysicalRadialAllOrderDeterminant

/-! Scaling a vector of confluent Schur coordinates back to the original
samples preserves its highest Newton stencil in the limit. -/

namespace CarrySchurProjectedTrace

open CarrySelfAdjointOperator Filter Topology
open scoped Matrix BigOperators
noncomputable section
set_option autoImplicit false

/-- The raw direction with its last divided-difference scale removed. -/
def scaledRawCoordinates (m : ℕ) (step : ℂ) (eta : Fin (m+1) → ℂ)
    (j : Fin (m+1)) : ℂ :=
  ∑ r : Fin (m+1), ((m.factorial : ℂ) * (r.val.factorial : ℂ)⁻¹ *
    completedGreenForwardWeight r.val j.val) * step ^ (m - r.val) * eta r

theorem scaledRawCoordinates_eq_transform (m : ℕ) (step : ℂ) (hn : step ≠ 0)
    (eta : Fin (m+1) → ℂ) (j : Fin (m+1)) :
    scaledRawCoordinates m step eta j =
      (m.factorial : ℂ) * step ^ m *
        ((completedGreenComplexForwardDifferenceTransform step (m+1)) *ᵥ eta) j := by
  unfold scaledRawCoordinates
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  change ((m.factorial : ℂ) * (r.val.factorial : ℂ)⁻¹ *
      completedGreenForwardWeight r.val j.val) * step ^ (m - r.val) * eta r =
    (m.factorial : ℂ) * step ^ m *
      (completedGreenComplexForwardDifferenceCoefficient step r.val j.val * eta r)
  unfold completedGreenComplexForwardDifferenceCoefficient
  have hp : step ^ m = step ^ r.val * step ^ (m - r.val) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp r.isLt)]
  rw [hp]
  have hf : (r.val.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero r.val
  field_simp [hf, pow_ne_zero _ hn]
  simp only [completedGreenForwardWeight]
  push_cast
  ring

/-- Any convergent vector in confluent coordinates whose last coefficient is
one has the last ordinary binomial stencil as its limit in raw coordinates. -/
theorem radial_scaled_raw_direction_tendsto (m : ℕ)
    (eta : ℕ → Fin (m+1) → ℂ) (eta₀ : Fin (m+1) → ℂ)
    (heta : Tendsto eta atTop (nhds eta₀)) (hlast : eta₀ (Fin.last m) = 1) :
    Tendsto (fun k j =>
      (m.factorial : ℂ) * (canonicalCompletedC3RadialSecondStep k) ^ m *
        ((completedGreenComplexForwardDifferenceTransform
          (canonicalCompletedC3RadialSecondStep k) (m+1)) *ᵥ eta k) j)
      atTop (nhds (fun j => completedGreenForwardWeight m j.val)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  have ht (r : Fin (m+1)) := (((canonicalCompletedC3RadialSecondStep_tendsto_zero.pow
    (m - r.val)).const_mul ((m.factorial : ℂ) * (r.val.factorial : ℂ)⁻¹ *
      completedGreenForwardWeight r.val j.val)).mul (tendsto_pi_nhds.mp heta r))
  have he (r : Fin (m+1)) :
      ((m.factorial : ℂ) * (r.val.factorial : ℂ)⁻¹ *
        completedGreenForwardWeight r.val j.val) * (0 : ℂ) ^ (m - r.val) * eta₀ r =
        (if r = Fin.last m then completedGreenForwardWeight m j.val else 0) := by
    by_cases hr : r = Fin.last m
    · subst r
      have hf : (m.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero m
      simp [hlast, hf]
    · have hne : r.val ≠ m := by
        intro he
        exact hr (Fin.ext he)
      have hrange : r.val ≤ m := Nat.lt_succ_iff.mp r.isLt
      rw [if_neg hr, zero_pow (show m - r.val ≠ 0 by omega), mul_zero, zero_mul]
  have hs := tendsto_finsetSum Finset.univ (fun r (_ : r ∈ Finset.univ) => ht r)
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  refine hs.congr' ?_
  filter_upwards with k
  exact scaledRawCoordinates_eq_transform m _ (canonicalCompletedC3RadialSecondStep_ne_zero k)
    (eta k) j

#print axioms radial_scaled_raw_direction_tendsto

end
end CarrySchurProjectedTrace
