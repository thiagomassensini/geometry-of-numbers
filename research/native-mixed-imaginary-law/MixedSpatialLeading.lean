import OddProfiles

namespace CarryMixedImaginary
open CarrySelfAdjointOperator CarryNativeTfvd CarryCriticalTfvd CarryStencilBoundary
open CarrySpatialCorrection CarryEnergyCorrection CarryOddEnergy NativeLaguerre
open scoped BigOperators InnerProductSpace ComplexConjugate
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

/-- Only TWO terms survive in the first excess degree, for arbitrary orders. -/
theorem divided_one_above (m n : ℕ) :
    dividedCoefficient m n (m+n+2)=
      (-1:ℂ)^n*(CarrySpatialCorrection.slope m-CarrySpatialCorrection.slope n) := by
  classical
  let f := fun l => (-1:ℂ)^l*differencePower m (m+n+2-1-l)*differencePower n l
  have hs : ({n,n+1} : Finset ℕ) ⊆ Finset.range (m+n+2) := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hz : ∀ l ∈ Finset.range (m+n+2), l ∉ ({n,n+1} : Finset ℕ) → f l=0 := by
    intro l hl he
    have hlp := Finset.mem_range.mp hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    unfold f
    by_cases hn : l < n
    · rw [difference_power_below hn, mul_zero]
    · rw [difference_power_below (show m+n+2-1-l < m by omega), mul_zero, zero_mul]
  have hsum := Finset.sum_subset hs hz
  change (∑ l ∈ Finset.range (m+n+2), f l)=_
  rw [← hsum]
  simp only [Finset.sum_insert (show n ∉ ({n+1} : Finset ℕ) by simp),
    Finset.sum_singleton, f, show m+n+2-1-n=m+1 by omega,
    show m+n+2-1-(n+1)=m by omega, difference_power_diagonal,
    difference_power_one_above, pow_succ]
  ring

/-- Fixed spatial coefficient, independent of the source moment signs. -/
def mixedSlope (r s : ℕ) : ℂ :=
  CarrySpatialCorrection.slope (2*s+1)-CarrySpatialCorrection.slope (2*r)

/-- The TWO ordered original Cauchy kernels, before phase calibration. -/
abbrev mixedStaticPair (w : ℕ → ℂ) (r s : ℕ) : ℂ :=
  kernel w (staticStencil (2*r)) (staticStencil (2*s+1))+
    kernel w (staticStencil (2*s+1)) (staticStencil (2*r))

theorem mixed_static_divided (r s p : ℕ) (hp : Odd p) :
    mixedStaticPair (monomialWeight p) r s=dividedCoefficient (2*r) (2*s+1) p :=
  static_odd_divided (1/2) (by norm_num) (by norm_num) _ _ _ hp

theorem mixed_static_below (r s l : ℕ) (hl : l < r+s+1) :
    mixedStaticPair (monomialWeight (2*l+1)) r s=0 := by
  rw [mixed_static_divided r s _ ⟨l,rfl⟩,
    divided_below (show 2*l+1 < (2*r)+(2*s+1)+1 by omega)]

theorem mixed_static_leading (r s : ℕ) :
    mixedStaticPair (monomialWeight (2*(r+s+1)+1)) r s=mixedSlope r s := by
  rw [mixed_static_divided r s _ ⟨r+s+1,rfl⟩,
    show 2*(r+s+1)+1=(2*r)+(2*s+1)+2 by omega, divided_one_above]
  norm_num [pow_add, pow_mul, mixedSlope]

/-- Original even/odd phases turn the difference into the ordered static sum. -/
theorem mixed_profile_phase (w : ℕ → ℂ) (r s : ℕ) :
    kernel w (nativeEvenProfile r) (nativeOddProfile s)-
      kernel w (nativeOddProfile s) (nativeEvenProfile r)=
        (-Complex.I)*(-1:ℂ)^(r+s)*mixedStaticPair w r s := by
  unfold nativeEvenProfile nativeOddProfile mixedStaticPair
  simp only [smul_smul, kernel_scale_inputs, map_mul, map_neg, map_pow, map_one, Complex.conj_I]
  rw [pow_add]
  ring

/-- Exact real factorization of the spatial coefficient; no moment is involved. -/
def mixedOrderWeight (r s : ℕ) : ℝ :=
  (2*(s:ℝ)-2*(r:ℝ)+1)*((r:ℝ)+(s:ℝ)+2)

theorem mixed_slope_eq_weight (r s : ℕ) : mixedSlope r s=(mixedOrderWeight r s:ℂ) := by
  unfold mixedSlope CarrySpatialCorrection.slope mixedOrderWeight
  push_cast
  ring

theorem mixed_weight_pos {r s : ℕ} (hrs : r ≤ s) : 0 < mixedOrderWeight r s := by
  have he : (r:ℝ) ≤ (s:ℝ) := by exact_mod_cast hrs
  unfold mixedOrderWeight
  exact mul_pos (by linarith) (by positivity)

theorem mixed_weight_neg {r s : ℕ} (hrs : s < r) : mixedOrderWeight r s < 0 := by
  have he : (s:ℝ)+1 ≤ (r:ℝ) := by exact_mod_cast hrs
  unfold mixedOrderWeight
  exact mul_neg_of_neg_of_pos (by linarith) (by positivity)

end
end CarryMixedImaginary
