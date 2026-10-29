import SourceDisc

namespace CarryEffectiveRadial
open CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem source_tail_term (z : ℂ) (M n : ℕ) :
    ‖(z^2)^(n+M)*(canonicalCompletedNativeLogDerivativeMoment (n+M):ℂ)‖ ≤
      ((22/175:ℝ)*((22/175:ℝ)*‖z‖^2)^M)*((22/175:ℝ)*‖z‖^2)^n := by
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
  calc
    (‖z‖^2)^(n+M)*|canonicalCompletedNativeLogDerivativeMoment (n+M)| ≤
      (‖z‖^2)^(n+M)*(22/175:ℝ)^(n+M+1) :=
        mul_le_mul_of_nonneg_left (source_coefficient_bound (n+M)) (by positivity)
    _ = _ := by simp only [pow_add,pow_succ,mul_pow]; ring

/-- Complete infinite tail, with an explicit radius and bound. -/
theorem source_tail_norm (z : ℂ) (hz : (22/175:ℝ)*‖z‖^2 < 1) (M : ℕ) :
    Summable (fun n : ℕ => (z^2)^(n+M)*(canonicalCompletedNativeLogDerivativeMoment (n+M):ℂ)) ∧
    ‖∑' n : ℕ, (z^2)^(n+M)*(canonicalCompletedNativeLogDerivativeMoment (n+M):ℂ)‖ ≤
      (22/175:ℝ)*((22/175:ℝ)*‖z‖^2)^M/(1-(22/175:ℝ)*‖z‖^2) := by
  have hg := (hasSum_geometric_of_lt_one (by positivity : (0:ℝ)≤(22/175:ℝ)*‖z‖^2) hz).mul_left
    ((22/175:ℝ)*((22/175:ℝ)*‖z‖^2)^M)
  have hs := hg.summable.of_norm_bounded (source_tail_term z M)
  refine ⟨hs,?_⟩
  have hb := hs.hasSum.norm_le_of_bounded hg (source_tail_term z M)
  simpa only [div_eq_mul_inv,mul_assoc] using hb

/-- Explicit bound for the ORIGINAL analytic response after any source
prefix. All omitted orders remain in the bounded infinite tail. -/
theorem native_response_prefix_error (z : ℂ) (hz : ‖z‖ < 1/4)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) (M : ℕ) :
    ‖completedNativeOperatorLogDerivative z-
      (2*z)*∑ n ∈ Finset.range M, (z^2)^n*(canonicalCompletedNativeLogDerivativeMoment n:ℂ)‖ ≤
      (2*‖z‖)*((22/175:ℝ)*((22/175:ℝ)*‖z‖^2)^M/(1-(22/175:ℝ)*‖z‖^2)) := by
  have hs : ‖z^2‖ < 4 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hq : (22/175:ℝ)*‖z‖^2 < 1 := by nlinarith [norm_nonneg z]
  have hh := source_series_hasSum (z^2) hs
  have he := hh.summable.sum_add_tsum_nat_add M
  rw [hh.tsum_eq] at he
  have hd : sourceSeries.sum (z^2)-
      (∑ n ∈ Finset.range M, (z^2)^n*(canonicalCompletedNativeLogDerivativeMoment n:ℂ))=
        ∑' n : ℕ, (z^2)^(n+M)*(canonicalCompletedNativeLogDerivativeMoment (n+M):ℂ) := by
    linear_combination -he
  rw [← source_response_eq_native z hz hF]
  unfold sourceResponse
  rw [← mul_sub,hd,norm_mul,norm_mul]
  norm_num only [Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (source_tail_norm z hq M).2 (by positivity)

end
end CarryEffectiveRadial
