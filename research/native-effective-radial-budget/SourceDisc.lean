import SourceSeries

namespace CarryEffectiveRadial
open CarrySelfAdjointOperator CPFormal.Analytic.Cp Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem quarter_disc_in_domain (z : ℂ) (hz : ‖z‖ < 1/4) :
    z ∈ completedNativeHeightDomain := by
  change 0 < (operatorHeightParameter z).re ∧ (operatorHeightParameter z).re < 1
  simp only [operatorHeightParameter,Complex.add_re,Complex.div_re,
    Complex.one_re,Complex.I_mul_re]
  norm_num
  have ha := Complex.abs_im_le_norm z
  have hb := neg_abs_le z.im
  have hc := le_abs_self z.im
  constructor <;> linarith

/-- Analytic continuation is applied to the PRODUCT identity, without
assuming that the characteristic is zero-free on a complex disc. -/
theorem source_response_product_on_disc (z : ℂ) (hz : ‖z‖ < 1/4) :
    sourceResponse z*completedNativeOperatorCharacteristic z+
      deriv completedNativeOperatorCharacteristic z=0 := by
  let f : ℂ → ℂ := fun w => sourceResponse w*completedNativeOperatorCharacteristic w+
    deriv completedNativeOperatorCharacteristic w
  have ha : AnalyticOnNhd ℂ f (Metric.ball 0 (1/4)) := by
    intro w hw
    have hn : ‖w‖ < 1/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hw
    have hf := completedNativeOperatorCharacteristic_analyticAt (quarter_disc_in_domain w hn)
    exact ((source_response_analytic w (by linarith)).fun_mul hf).fun_add hf.deriv
  have he : f =ᶠ[nhds 0] (fun _ => 0) := by
    have hn := (completedNativeOperatorCharacteristic_analyticAt
      zero_mem_completedNativeHeightDomain).continuousAt.eventually_ne
        completedNativeOperatorCharacteristic_zero_ne_zero
    filter_upwards [source_response_local_eq,hn] with w hw hn
    dsimp [f]
    rw [hw]
    unfold completedNativeOperatorLogDerivative
    field_simp [hn]
    ring
  exact ha.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
    (convex_ball (0:ℂ) (1/4:ℝ)).isPreconnected (by simp) he
      (by simpa only [Metric.mem_ball,dist_zero_right] using hz)

theorem source_response_eq_native (z : ℂ) (hz : ‖z‖ < 1/4)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    sourceResponse z=completedNativeOperatorLogDerivative z := by
  have hp := source_response_product_on_disc z hz
  unfold completedNativeOperatorLogDerivative
  apply (eq_div_iff hF).mpr
  linear_combination hp

/-- An explicit radius for the ORIGINAL full-height response series. Only
nonvanishing at the evaluation point is needed, not a zero-set hypothesis. -/
theorem native_response_hasSum_on_disc (z : ℂ) (hz : ‖z‖ < 1/4)
    (hF : completedNativeOperatorCharacteristic z ≠ 0) :
    HasSum (fun n : ℕ => (2*z)*((z^2)^n*(canonicalCompletedNativeLogDerivativeMoment n:ℂ)))
      (completedNativeOperatorLogDerivative z) := by
  have hs : ‖z^2‖ < 4 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hh := (source_series_hasSum (z^2) hs).mul_left (2*z)
  rw [← source_response_eq_native z hz hF]
  exact hh

/-- Actual imaginary radial points are nonzero by the source's existing
real-strip nonvanishing, not by a Hankel or spectral premise. -/
theorem imaginary_characteristic_ne_zero (y : ℝ) (hy : |y| < 1/4) :
    completedNativeOperatorCharacteristic (Complex.I*(y:ℂ)) ≠ 0 := by
  have hz : ‖Complex.I*(y:ℂ)‖ < 1/4 := by simpa [norm_mul] using hy
  have hd := quarter_disc_in_domain _ hz
  have hs : operatorHeightParameter (Complex.I*(y:ℂ)) ∈ genuineCriticalStrip := hd
  have he : operatorHeightParameter (Complex.I*(y:ℂ))=((1/2-y:ℝ):ℂ) := by
    unfold operatorHeightParameter
    push_cast
    ring_nf
    norm_num [Complex.I_sq]
    ring
  unfold completedNativeOperatorCharacteristic
  apply mul_ne_zero (nativeXiCompletionFactor_ne_zero hs)
  rw [nativeScalar_eq_genuineContinuation hs,he]
  have hn := (abs_lt.mp hy)
  exact genuineContinuation_ofReal_ne_zero (σ := 1/2-y) (by linarith) (by linarith)

end
end CarryEffectiveRadial
