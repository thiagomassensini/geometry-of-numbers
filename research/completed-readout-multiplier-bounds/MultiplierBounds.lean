import DressingBounds

/-! Closed unconditional bounds for the literal completed readout multipliers.
All orders are normalized Taylor jets; no moment or pivot sign is a premise. -/
namespace CarryReadoutBounds
open GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.BaseTwoCompletion
open CarryCellTail CarryFourthTail CarryMaterialParts
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def complexOrdinaryMultiplier (w : ℂ) : ℂ := -logDeriv complexDressing w/(2*complexSignal w)
def complexClockMultiplier (w : ℂ) : ℂ := Complex.I/(2*complexSignal w)

theorem complex_signal_analytic (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) : AnalyticAt ℂ complexSignal w :=
  complex_signal_differentiableOn.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))

theorem complex_ordinary_multiplier_analytic (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    AnalyticAt ℂ complexOrdinaryMultiplier w := by
  have hd := complex_dressing_analytic w hw
  exact ((hd.deriv.div hd (complex_dressing_nonzero w hw)).neg).div
    (analyticAt_const.mul (complex_signal_analytic w (by linarith)))
    (mul_ne_zero (by norm_num) (signal_nonzero w (by linarith)))

theorem complex_clock_multiplier_analytic (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) :
    AnalyticAt ℂ complexClockMultiplier w :=
  analyticAt_const.div (analyticAt_const.mul (complex_signal_analytic w hw))
    (mul_ne_zero (by norm_num) (signal_nonzero w hw.le))

theorem complex_ordinary_multiplier_bound (w : ℂ) (hw : ‖w‖ ≤ (1/8:ℝ)) :
    ‖complexOrdinaryMultiplier w‖ ≤ 8192 := by
  have hi := inverse_signal_bound w (by linarith)
  unfold complexOrdinaryMultiplier
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_neg]
  norm_num
  have h := mul_le_mul (dressing_log_bound w hw) hi (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 8192)
  simp only [norm_inv] at h
  nlinarith

theorem complex_clock_multiplier_bound (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖complexClockMultiplier w‖ ≤ 1 := by
  have hi := inverse_signal_bound w hw
  unfold complexClockMultiplier
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
  norm_num
  simp only [norm_inv] at hi
  linarith

theorem complex_dressing_real (t : ℝ) : complexDressing (t:ℂ) = baseTwoCanonicalDressingScalar t := rfl

theorem dressing_deriv_real (t : ℝ) (ht : |t| ≤ (1/4:ℝ)) :
    deriv baseTwoCanonicalDressingScalar t = deriv complexDressing (t:ℂ) := by
  have h := (complex_dressing_analytic (t:ℂ) (by simpa using ht)).differentiableAt.hasDerivAt.comp_ofReal
  change HasDerivAt baseTwoCanonicalDressingScalar (deriv complexDressing (t:ℂ)) t at h
  exact h.deriv

theorem clock_multiplier_real (t : ℝ) : complexClockMultiplier (t:ℂ) = clockMultiplier t := by
  rw [complexClockMultiplier, complex_signal_real, clockMultiplier,
    baseTwoCanonicalResponse_eq_dressing_mul_signal]
  have hD := baseTwoCanonicalDressingScalar_ne_zero t
  have he : 2*(baseTwoCanonicalDressingScalar t*baseTwoCriticalCompleteSignal t) =
      baseTwoCanonicalDressingScalar t*(2*baseTwoCriticalCompleteSignal t) := by ring
  rw [he, mul_comm Complex.I, mul_div_mul_left _ _ hD]

theorem ordinary_multiplier_real (t : ℝ) (ht : |t| ≤ (1/4:ℝ)) :
    complexOrdinaryMultiplier (t:ℂ) = ordinaryMultiplier t := by
  rw [complexOrdinaryMultiplier, logDeriv_apply, complex_dressing_real,
    complex_signal_real, ordinaryMultiplier, dressing_deriv_real t ht,
    baseTwoCanonicalResponse_eq_dressing_mul_signal, neg_div, div_div]
  ring

theorem ordinary_multiplier_jet_bound (m : ℕ) :
    ‖rJet m ordinaryMultiplier‖ ≤ 8192*8^m := by
  have he : ordinaryMultiplier =ᶠ[nhds 0] fun t : ℝ => complexOrdinaryMultiplier (t:ℂ) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1/4)] with t ht
    exact (ordinary_multiplier_real t (by
      exact (show |t| < (1/4:ℝ) by simpa using ht).le)).symm
  have hj := real_jet_complex he (complex_ordinary_multiplier_analytic 0 (by norm_num)) m
  change rJet m ordinaryMultiplier = _ at hj
  rw [hj]
  have hf : DiffContOnCl ℂ complexOrdinaryMultiplier (Metric.ball 0 (1/8:ℝ)) :=
    (show DifferentiableOn ℂ complexOrdinaryMultiplier (Metric.closedBall 0 (1/8:ℝ)) from
      fun w hw => (complex_ordinary_multiplier_analytic w (by
        have hh : ‖w‖ ≤ (1/8:ℝ) := by simpa using hw
        linarith)).differentiableAt.differentiableWithinAt).diffContOnCl_ball (by intro w hw; exact hw)
  have h := normalized_cauchy (by norm_num : (0:ℝ)<1/8) hf
    (fun w hw => complex_ordinary_multiplier_bound w hw.le) m
  simpa only [one_div, inv_pow, div_inv_eq_mul] using h

theorem clock_multiplier_jet_bound (m : ℕ) :
    ‖rJet m clockMultiplier‖ ≤ (4:ℝ)^m := by
  have hj := real_jet_complex (.of_forall (fun t => (clock_multiplier_real t).symm))
    (complex_clock_multiplier_analytic 0 (by norm_num)) m
  change rJet m clockMultiplier = _ at hj
  rw [hj]
  have hf : DiffContOnCl ℂ complexClockMultiplier (Metric.ball 0 (1/4:ℝ)) :=
    (show DifferentiableOn ℂ complexClockMultiplier (Metric.closedBall 0 (1/4:ℝ)) from
      fun w hw => (complex_clock_multiplier_analytic w (by
        have hh : ‖w‖ ≤ (1/4:ℝ) := by simpa using hw
        linarith)).differentiableAt.differentiableWithinAt).diffContOnCl_ball (by intro w hw; exact hw)
  have h := normalized_cauchy (by norm_num : (0:ℝ)<1/4) hf
    (fun w hw => complex_clock_multiplier_bound w (by linarith)) m
  simpa only [one_div, inv_pow, div_inv_eq_mul, one_mul] using h

end
end CarryReadoutBounds
