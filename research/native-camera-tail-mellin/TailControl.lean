import CompletedTrace

namespace CarryCameraTail
open CarryMaterialTheta MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem camera_tail_tendsto_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun M : ℕ => cameraHeatTail M x) atTop (𝓝 0) := by
  have hsum := summable_camera_blocks 0 hx
  have heq (M : ℕ) : cameraHeatTail M x =
      cameraHeatTail 0 x - cameraHeatPrefix 0 M x := by
    have h := hsum.sum_add_tsum_nat_add M
    simp only [cameraHeatTail, cameraHeatPrefix, Nat.add_zero] at h ⊢
    linear_combination h
  have hl : Tendsto (fun M : ℕ => cameraHeatTail 0 x - cameraHeatPrefix 0 M x)
      atTop (𝓝 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := cameraHeatTail 0 x)).sub (camera_prefix_tendsto 0 hx)
  exact hl.congr' (Eventually.of_forall fun M => (heq M).symm)

def tailErrorIntegrand (M : ℕ) (s : ℂ) (x : ℝ) : ℝ :=
  ‖(x : ℂ)^(s/2-1) • cameraHeatTail M x‖ +
    ‖(x : ℂ)^(s/2-1) • (Real.log x • cameraHeatTail M x)‖

def heatErrorMajorant (s : ℂ) (x : ℝ) : ℝ :=
  ‖(x : ℂ)^(s/2-1) • heatSample 2 x‖ +
    ‖(x : ℂ)^(s/2-1) • (Real.log x • heatSample 2 x)‖

theorem heat_error_majorant_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (heatErrorMajorant s) (Ioi 0) := by
  have hm : AEStronglyMeasurable (heatSample 2) (volume.restrict (Ioi 0)) := by
    have hc : Continuous (heatSample 2) := by unfold heatSample; fun_prop
    exact hc.aestronglyMeasurable
  have hlog := (bounded_heat_mellin_hasDerivAt (heatSample 2) 2 (by omega)
    1 zero_le_one hm (by
      intro x _
      simp only [heatSample, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
        heat, one_mul]
      exact le_rfl
      ) hs).1
  exact (heat_mellin_convergent 2 (by omega) hs).norm.add hlog.norm

theorem tail_error_integrand_eq_weight (M : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    tailErrorIntegrand M s x =
      x^((s/2).re-1)*(1+|Real.log x|)*‖cameraHeatTail M x‖ := by
  simp only [tailErrorIntegrand, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.sub_re, Complex.one_re, Real.norm_eq_abs]
  ring

theorem tail_error_integrand_le (M : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    tailErrorIntegrand M s x ≤ heatErrorMajorant s x := by
  have h : ‖cameraHeatTail M x‖ ≤ heat 2 x :=
    (camera_tail_norm_le M hx).trans (heat_antitone hx.le (by omega : 2 ≤ 3*M+2))
  simp only [tailErrorIntegrand, heatErrorMajorant, norm_smul, heatSample,
    Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  change ‖(x : ℂ)^(s/2-1)‖*‖cameraHeatTail M x‖ +
    ‖(x : ℂ)^(s/2-1)‖*(|Real.log x| * ‖cameraHeatTail M x‖) ≤
    ‖(x : ℂ)^(s/2-1)‖*heat 2 x + ‖(x : ℂ)^(s/2-1)‖*(|Real.log x| * heat 2 x)
  gcongr

/-- The operational value-plus-first-jet tail error tends to zero in the
weighted L1 norm needed by Mellin. Cancellation precedes the integral. -/
theorem weighted_camera_tail_error_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => ∫ x : ℝ in Ioi 0,
      x^((s/2).re-1)*(1+|Real.log x|)*‖cameraHeatTail M x‖) atTop (𝓝 0) := by
  have hd : Tendsto (fun M : ℕ => ∫ x : ℝ in Ioi 0, tailErrorIntegrand M s x)
      atTop (𝓝 (∫ _x : ℝ in Ioi 0, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (heatErrorMajorant s)
      (fun M => ((camera_tail_mellin_convergent M hs).norm.add
        (tail_log_mellin_hasDerivAt M hs).1.norm).aestronglyMeasurable)
      (heat_error_majorant_integrable hs)
    · intro M
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        change 0 ≤ ‖_‖ + ‖_‖
        positivity)]
      exact tail_error_integrand_le M s hx
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have h := camera_tail_tendsto_zero hx
      have h₁ := (tendsto_const_nhds (x := (x : ℂ)^(s/2-1))).smul h
      have h₂ := (tendsto_const_nhds (x := (x : ℂ)^(s/2-1))).smul
        ((tendsto_const_nhds (x := Real.log x)).smul h)
      have hlim := h₁.norm.add h₂.norm
      have hzero : ‖(x : ℂ)^(s/2-1) • (0 : ℂ)‖ +
          ‖(x : ℂ)^(s/2-1) • (Real.log x • (0 : ℂ))‖ = 0 := by simp
      rw [hzero] at hlim
      exact hlim
  have heq (M : ℕ) : (∫ x : ℝ in Ioi 0, tailErrorIntegrand M s x) =
      ∫ x : ℝ in Ioi 0, x^((s/2).re-1)*(1+|Real.log x|)*‖cameraHeatTail M x‖ :=
    setIntegral_congr_fun measurableSet_Ioi (fun _ hx => tail_error_integrand_eq_weight M s hx)
  simpa only [heq, integral_zero] using hd

end
end CarryCameraTail
