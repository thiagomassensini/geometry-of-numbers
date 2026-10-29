import NativeCoefficient

namespace CarryCurvatureGreen
open CarrySelfAdjointOperator CarryNativeTfvd CarryCommutatorControl CarryCriticalTfvd NativeLaguerre
open Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem leading_coefficient_formula (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    poleFour true eta h0 h1 = 2*canonicalCompletedNativeLogDerivativeMoment 0*nativeU1 eta h0 h1 := rfl

/-- No moment sign is used to extract the actual mixed coefficient. -/
theorem mixed_scaled_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    Tendsto (fun k : ℕ => mixedEnergy eta h0 h1 k (criticalInput k a)/((k : ℝ)+1)^4)
      atTop (nhds (poleFour true eta h0 h1)) := by
  obtain ⟨R,hR,he⟩ := complete_tfvd_expansion
  have ht := radial_step_tendsto
  have hr := (sector_error_continuous true eta h0 h1 R hR a).tendsto.comp ht
  have hh := (((tendsto_const_nhds (x := poleFour true eta h0 h1)).add
    ((ht.pow 2).mul_const (poleTwo true eta h0 h1 a))).add
    ((ht.pow 4).mul_const (finitePart true eta h0 h1 a))).add ((ht.pow 6).mul hr)
  have hv : Tendsto (fun k : ℕ => poleFour true eta h0 h1 +
      radialStep k^2*poleTwo true eta h0 h1 a + radialStep k^4*finitePart true eta h0 h1 a +
      radialStep k^6*sectorError true eta h0 h1 R a (radialStep k)) atTop
      (nhds (poleFour true eta h0 h1)) := by simpa [Function.comp_def] using hh
  apply hv.congr'
  filter_upwards [he eta h0 h1 a] with k hk
  rw [hk.1]
  unfold radialStep
  have hn : (k : ℝ)+1≠0 := by positivity
  field_simp [hn]

theorem bulk_boundary_scaled_limit (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    Tendsto (fun k : ℕ => bulkBoundaryEnergy eta h0 h1 k (criticalInput k a)/((k : ℝ)+1)^4)
      atTop (nhds (-poleFour true eta h0 h1)) := by
  have hq := (full_critical_limit eta h0 h1 a).mul (radial_step_tendsto.pow 4)
  have hx := hq.sub (mixed_scaled_limit eta h0 h1 a)
  have hv : Tendsto (fun k : ℕ => fullEnergy k (criticalInput k a)*radialStep k^4-
      mixedEnergy eta h0 h1 k (criticalInput k a)/((k : ℝ)+1)^4)
      atTop (nhds (-poleFour true eta h0 h1)) := by simpa using hx
  apply hv.congr'
  filter_upwards [radial_weight_difference_eventually 4] with k hk
  rw [full_split eta h0 h1 k _ (critical_input_support k a) hk]
  unfold radialStep
  have hn : (k : ℝ)+1≠0 := by positivity
  field_simp [hn]
  ring

/-- The ONLY sign imported below is the already certified h0>0. The geometric
U1 factorization and lower bound above do not depend on this theorem. -/
theorem leading_coefficient_pos (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    0 < poleFour true eta h0 h1 := by
  rw [leading_coefficient_formula]
  exact mul_pos (mul_pos (by norm_num) canonicalCompletedNativeLogDerivativeMoment_zero_pos)
    (native_u1_pos eta h0 h1)

theorem leading_coefficient_lower_bound (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) :
    (1-eta^2)/120*canonicalCompletedNativeLogDerivativeMoment 0 ≤ poleFour true eta h0 h1 := by
  have hh := canonicalCompletedNativeLogDerivativeMoment_zero_pos
  have hb := mul_le_mul_of_nonneg_left (native_u1_lower_bound eta h0 h1)
    (show 0≤2*canonicalCompletedNativeLogDerivativeMoment 0 by positivity)
  rw [leading_coefficient_formula]
  nlinarith

theorem mixed_eventually_positive (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    ∀ᶠ k : ℕ in atTop, 0 < mixedEnergy eta h0 h1 k (criticalInput k a) := by
  have hp := (mixed_scaled_limit eta h0 h1 a).eventually
    (eventually_gt_nhds (leading_coefficient_pos eta h0 h1))
  filter_upwards [hp] with k hk
  by_contra hn
  have hz := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
    (show 0≤((k : ℝ)+1)^4 by positivity)
  linarith

theorem bulk_boundary_eventually_negative (eta : ℝ) (h0 : 0 < eta) (h1 : eta < 1) (a : ℝ) :
    ∀ᶠ k : ℕ in atTop, bulkBoundaryEnergy eta h0 h1 k (criticalInput k a) < 0 := by
  have hp := (bulk_boundary_scaled_limit eta h0 h1 a).eventually
    (eventually_lt_nhds (show -poleFour true eta h0 h1 < 0 by linarith [leading_coefficient_pos eta h0 h1]))
  filter_upwards [hp] with k hk
  by_contra hn
  have hz := div_nonneg (le_of_not_gt hn) (show 0≤((k : ℝ)+1)^4 by positivity)
  linarith

end
end CarryCurvatureGreen
