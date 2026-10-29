import TailControls
import CarrySelfAdjointOperator.CompletedNativeLogCoefficientMajorant
import CarrySelfAdjointOperator.CompletedNativeEvenCoordinateResolventBridge
import Mathlib.Analysis.Analytic.Uniqueness

namespace CarryEffectiveRadial
open CarrySelfAdjointOperator Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

/-- Source coefficients, unchanged. This is a scalar series, not a new
source or a moment-defined physical state. -/
def sourceSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (canonicalCompletedNativeLogDerivativeMoment n:ℂ))

theorem source_coefficient_bound (n : ℕ) :
    |canonicalCompletedNativeLogDerivativeMoment n|≤(22/175:ℝ)^(n+1) := by
  have h := canonicalCompletedNativeLogDerivativeMoment_sharp_decay n
  have hp := pow_nonneg (by norm_num : (0:ℝ)≤1/25) (n+1)
  linarith

theorem source_series_radius : (4:ENNReal)≤ sourceSeries.radius := by
  apply sourceSeries.le_radius_of_bound (1:ℝ) (r := (4:NNReal))
  intro n
  rw [sourceSeries,FormalMultilinearSeries.ofScalars_norm,Complex.norm_real,Real.norm_eq_abs]
  calc
    |canonicalCompletedNativeLogDerivativeMoment n| *(4:ℝ)^n ≤
        (22/175:ℝ)^(n+1)*4^n := mul_le_mul_of_nonneg_right (source_coefficient_bound n) (by positivity)
    _ = (22/175:ℝ)*(88/175:ℝ)^n := by rw [pow_succ,mul_right_comm,← mul_pow]; norm_num; ring
    _ ≤ 1 := by
      have hp : (88/175:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num : (0:ℝ)≤88/175) (by norm_num : (88/175:ℝ)≤1)
      nlinarith

theorem source_series_positive_radius : 0<sourceSeries.radius :=
  lt_of_lt_of_le (by norm_num : (0:ENNReal)<4) source_series_radius

theorem source_series_mem (u : ℂ) (hu : ‖u‖<4) : u∈Metric.eball 0 sourceSeries.radius := by
  change edist u 0 < sourceSeries.radius
  apply lt_of_lt_of_le _ source_series_radius
  simpa [Metric.mem_eball,edist_dist] using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<4)).mpr hu

theorem source_series_analytic (u : ℂ) (hu : ‖u‖<4) : AnalyticAt ℂ sourceSeries.sum u :=
  (sourceSeries.hasFPowerSeriesOnBall source_series_positive_radius).analyticAt_of_mem
    (source_series_mem u hu)

theorem source_series_hasSum (u : ℂ) (hu : ‖u‖<4) :
    HasSum (fun n : ℕ => u^n*(canonicalCompletedNativeLogDerivativeMoment n:ℂ)) (sourceSeries.sum u) := by
  simpa [sourceSeries,FormalMultilinearSeries.ofScalars_apply_eq] using
    sourceSeries.hasSum (source_series_mem u hu)

theorem source_series_local_eq : sourceSeries.sum =ᶠ[nhds 0] completedNativeLogDerivative := by
  have hu : ∀ᶠ u : ℂ in nhds 0, ‖u‖<4 := by
    have hc : ContinuousAt (fun u : ℂ => ‖u‖) 0 := continuous_norm.continuousAt
    exact hc.tendsto.eventually_lt tendsto_const_nhds (by norm_num)
  filter_upwards [hu,completedNativeLogDerivative_eventually_hasSum_canonical] with u hu hh
  exact (source_series_hasSum u hu).unique hh

/-- The unchanged full-height response reconstructed with its fixed 2z. -/
def sourceResponse (z : ℂ) : ℂ := 2*z*sourceSeries.sum (z^2)

theorem source_response_analytic (z : ℂ) (hz : ‖z‖<1) : AnalyticAt ℂ sourceResponse z := by
  have hs : ‖z^2‖<4 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  exact (analyticAt_const.fun_mul analyticAt_id).fun_mul
    ((source_series_analytic (z^2) hs).fun_comp_of_eq (by fun_prop) rfl)

theorem source_response_local_eq : sourceResponse =ᶠ[nhds 0] completedNativeOperatorLogDerivative := by
  have ht : Tendsto (fun z : ℂ => z^2) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun z : ℂ => z^2) 0 := by fun_prop
    simpa using hc.tendsto
  filter_upwards [ht.eventually source_series_local_eq,
    completedNativeOperatorLogDerivative_eventuallyEq_evenCoordinate] with z hs hq
  unfold sourceResponse
  rw [hs,hq]

end
end CarryEffectiveRadial
