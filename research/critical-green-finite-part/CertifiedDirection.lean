import RemainderControl
import IntegralOrientation
import CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy

namespace CarryGreenFinitePart
open CarryInteriorGreen CarrySelfAdjointOperator Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Reuse of the original finite theta-source inequality from PR43.
This is not an all-order claim and is not used in the analytic expansion. -/
theorem critical_correction_negative : correctionTerm criticalParameter<0 := by
  have h0 := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have hn : 0<canonicalCompletedNativeLogDerivativeMoment 1^3-
      40*canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 1*
        canonicalCompletedNativeLogDerivativeMoment 2+
      14*canonicalCompletedNativeLogDerivativeMoment 0^2*canonicalCompletedNativeLogDerivativeMoment 3 := by
    have h := CarryCriticalMixed.source_correction_numerator_pos
    change 0<2*canonicalCompletedNativeLogDerivativeMoment 1^3-
      80*canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 1*
        canonicalCompletedNativeLogDerivativeMoment 2+
      28*canonicalCompletedNativeLogDerivativeMoment 0^2*canonicalCompletedNativeLogDerivativeMoment 3 at h
    nlinarith
  rw [critical_correction_formula (ne_of_gt h0)]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hn) (sq_pos_of_pos h0)

/-- The old source inequality is stronger than positivity of this pivot.
No later H6/K6 certificate is consumed. -/
theorem critical_finite_term_positive : 0<finiteTerm criticalParameter := by
  have h0 := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have h := CarryCriticalMixed.source_nonlinear_margin_pos
  change 0<canonicalCompletedNativeLogDerivativeMoment 0*canonicalCompletedNativeLogDerivativeMoment 2-
    2*canonicalCompletedNativeLogDerivativeMoment 1^2 at h
  rw [finite_term_critical (ne_of_gt h0),first_source_schur_eq]
  apply sub_pos.mpr
  apply (div_lt_iff₀ h0).mpr
  nlinarith [sq_nonneg (canonicalCompletedNativeLogDerivativeMoment 1)]

theorem critical_green_scaled_correction (η : ℝ) (hη0 : 0<η) (hη1 : η<1) :
    Tendsto (fun (k : ℕ) => ((k : ℝ)+1)^2*(greenBalance η criticalParameter k-
      sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 0 1)) atTop
      (nhds (correctionTerm criticalParameter)) := by
  simpa only [finite_term_critical (ne_of_gt canonicalCompletedNativeLogDerivativeMoment_zero_pos)] using
    green_correction_limit η hη0 hη1 criticalParameter

/-- Eventually positive and strictly below the original Schur limit.
Neither monotonicity nor a numerical threshold is asserted. -/
theorem critical_green_eventually_between (η : ℝ) (hη0 : 0<η) (hη1 : η<1) :
    ∀ᶠ k : ℕ in atTop, 0<greenBalance η criticalParameter k ∧
      greenBalance η criticalParameter k<sourceMomentSchur canonicalCompletedNativeLogDerivativeMoment 0 1 := by
  have hp := (green_finite_term_limit η hη0 hη1 criticalParameter).eventually
    (lt_mem_nhds critical_finite_term_positive)
  have hc := (green_correction_limit η hη0 hη1 criticalParameter).eventually
    (gt_mem_nhds critical_correction_negative)
  filter_upwards [hp,hc] with k hk hc
  refine ⟨hk,?_⟩
  have hn : 0<((k : ℝ)+1)^2 := by positivity
  have hd : greenBalance η criticalParameter k-finiteTerm criticalParameter<0 :=
    (mul_lt_mul_iff_of_pos_left hn).mp (by simpa only [mul_zero] using hc)
  rw [← finite_term_critical (ne_of_gt canonicalCompletedNativeLogDerivativeMoment_zero_pos)]
  linarith

end
end CarryGreenFinitePart
