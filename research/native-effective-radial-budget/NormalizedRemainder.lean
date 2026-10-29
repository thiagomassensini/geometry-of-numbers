import ExplicitSourceTail
import Mathlib.Analysis.Complex.Liouville

namespace CarryEffectiveRadial
open CarrySelfAdjointOperator Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

def shiftedSeries (M : ℕ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (canonicalCompletedNativeLogDerivativeMoment (n+M):ℂ))

theorem shifted_coefficient_bound (M n : ℕ) :
    |canonicalCompletedNativeLogDerivativeMoment (n+M)| ≤
      (22/175:ℝ)^(M+1)*(22/175:ℝ)^n := by
  simpa only [pow_add,pow_succ,mul_comm,mul_left_comm,mul_assoc] using source_coefficient_bound (n+M)

theorem shifted_series_radius (M : ℕ) : (4:ENNReal) ≤ (shiftedSeries M).radius := by
  apply (shiftedSeries M).le_radius_of_bound (1:ℝ) (r := (4:NNReal))
  intro n
  rw [shiftedSeries,FormalMultilinearSeries.ofScalars_norm,Complex.norm_real,Real.norm_eq_abs]
  calc
    |canonicalCompletedNativeLogDerivativeMoment (n+M)| *4^n ≤
        ((22/175:ℝ)^(M+1)*(22/175:ℝ)^n)*4^n :=
      mul_le_mul_of_nonneg_right (shifted_coefficient_bound M n) (by positivity)
    _ = (22/175:ℝ)^(M+1)*(88/175:ℝ)^n := by rw [mul_assoc,← mul_pow]; norm_num
    _ ≤ 1 := mul_le_one₀
      (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))

theorem shifted_series_mem (M : ℕ) (u : ℂ) (hu : ‖u‖ < 4) :
    u ∈ Metric.eball 0 (shiftedSeries M).radius := by
  change edist u 0 < (shiftedSeries M).radius
  apply lt_of_lt_of_le _ (shifted_series_radius M)
  simpa [edist_dist] using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<4)).mpr hu

theorem shifted_series_hasSum (M : ℕ) (u : ℂ) (hu : ‖u‖ < 4) :
    HasSum (fun n => u^n*(canonicalCompletedNativeLogDerivativeMoment (n+M):ℂ))
      ((shiftedSeries M).sum u) := by
  simpa [shiftedSeries,FormalMultilinearSeries.ofScalars_apply_eq] using
    (shiftedSeries M).hasSum (shifted_series_mem M u hu)

def sourceRemainder (M : ℕ) (z : ℂ) : ℂ := 2*(shiftedSeries M).sum (z^2)

/-- The normalized remainder is identified with the ORIGINAL response at
every regular point of the explicit disc, not just with matching jets. -/
theorem native_response_exact_remainder (M : ℕ) (z : ℂ) (hz : ‖z‖ < 1/4)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    completedNativeOperatorLogDerivative z =
      (2*z)*(∑ n ∈ Finset.range M, (z^2)^n*(canonicalCompletedNativeLogDerivativeMoment n:ℂ))+
        z^(2*M+1)*sourceRemainder M z := by
  have hn : ‖z^2‖ < 4 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hh := source_series_hasSum (z^2) hn
  have ht : HasSum (fun n : ℕ => (z^2)^(n+M)*(canonicalCompletedNativeLogDerivativeMoment (n+M):ℂ))
      ((z^2)^M*(shiftedSeries M).sum (z^2)) := by
    convert (shifted_series_hasSum M (z^2) hn).mul_left ((z^2)^M) using 1
    all_goals try rfl
    funext n
    rw [pow_add]
    ring
  have he := hh.summable.sum_add_tsum_nat_add M
  rw [ht.tsum_eq,hh.tsum_eq] at he
  rw [← source_response_eq_native z hz hF]
  unfold sourceResponse sourceRemainder
  rw [← he]
  simp only [pow_add,pow_one,pow_mul]
  ring

theorem source_remainder_analytic (M : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (sourceRemainder M) z := by
  have hs : ‖z^2‖ < 4 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hp := (shiftedSeries M).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num : (0:ENNReal)<4) (shifted_series_radius M))
  exact analyticAt_const.fun_mul ((hp.analyticAt_of_mem (shifted_series_mem M _ hs)).fun_comp_of_eq
    (by fun_prop) rfl)

theorem source_remainder_norm_le_one (M : ℕ) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖sourceRemainder M z‖ ≤ 1 := by
  have hq : (22/175:ℝ)*‖z‖^2 < 1 := by nlinarith [norm_nonneg z]
  have hs : ‖z^2‖ < 4 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have ht (n : ℕ) : ‖(z^2)^n*(canonicalCompletedNativeLogDerivativeMoment (n+M):ℂ)‖ ≤
      (22/175:ℝ)^(M+1)*((22/175:ℝ)*‖z‖^2)^n := by
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ (‖z‖^2)^n*((22/175:ℝ)^(M+1)*(22/175:ℝ)^n) :=
        mul_le_mul_of_nonneg_left (shifted_coefficient_bound M n) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  have hg := (hasSum_geometric_of_lt_one (by positivity : (0:ℝ)≤(22/175:ℝ)*‖z‖^2) hq).mul_left
    ((22/175:ℝ)^(M+1))
  have hb := (shifted_series_hasSum M (z^2) hs).norm_le_of_bounded hg ht
  have hp : (22/175:ℝ)^(M+1) ≤ 22/175 := by
    rw [pow_succ]
    exact mul_le_of_le_one_left (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))
  have hden : 0 < 1-(22/175:ℝ)*‖z‖^2 := sub_pos.mpr hq
  have hnorm : ‖(shiftedSeries M).sum (z^2)‖ ≤ (22/175:ℝ)/(1-(22/175:ℝ)*‖z‖^2) := by
    simpa only [div_eq_mul_inv] using hb.trans
      (mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr hden.le))
  unfold sourceRemainder
  rw [norm_mul]
  norm_num only [Complex.norm_ofNat]
  have hhalf : (22/175:ℝ)/(1-(22/175:ℝ)*‖z‖^2) ≤ 1/2 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [norm_nonneg z]
  have hbhalf := hnorm.trans hhalf
  linarith

/-- Effective derivative bound on the full omitted analytic source. -/
theorem source_remainder_deriv_bound (M : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1/4) :
    ‖deriv (sourceRemainder M) z‖ ≤ 4 := by
  have ha : AnalyticOnNhd ℂ (sourceRemainder M) (Metric.closedBall z (1/4)) := by
    intro w hw
    apply source_remainder_analytic M w
    have hd := (Metric.mem_closedBall.mp hw)
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel] at ht
    rw [dist_eq_norm] at hd
    linarith
  have hd : DiffContOnCl ℂ (sourceRemainder M) (Metric.ball z (1/4)) :=
    (ha.differentiableOn.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hb : ∀ w ∈ Metric.sphere z (1/4), ‖sourceRemainder M w‖ ≤ 1 := by
    intro w hw
    apply source_remainder_norm_le_one M w
    have he := Metric.mem_sphere.mp hw
    have ht := norm_add_le (w-z) z
    rw [sub_add_cancel] at ht
    rw [dist_eq_norm] at he
    linarith
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1/4) hd hb
  norm_num at hh
  exact hh

end
end CarryEffectiveRadial
