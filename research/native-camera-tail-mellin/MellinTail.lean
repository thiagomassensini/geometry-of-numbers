import CameraHeatTail

namespace CarryCameraTail
open CarryMaterialTheta CarrySelfAdjointOperator CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem heat_mellin_convergent (n : ℕ) (hn : 0 < n) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (heatSample n) (s/2) := by
  have hs' : 0 < (s/2).re := by simpa using half_pos hs
  have hzero : MellinConvergent (fun x : ℝ => (Real.exp (-x) : ℂ)) (s/2) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using
      Complex.GammaIntegral_convergent hs'
  have ha : 0 < Real.pi*(n : ℝ)^2 := by positivity
  have h := (MellinConvergent.comp_mul_left (s := s/2) ha).2 hzero
  have hf : (fun x : ℝ => (Real.exp (-(Real.pi*(n : ℝ)^2*x)) : ℂ)) =
      heatSample n := by
    funext x
    simp only [heatSample]
    congr 2
    ring
  simpa only [hf] using h

theorem camera_block_mellin_convergent (m : ℕ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (cameraHeatBlock m) (s/2) := by
  exact (hasMellin_add
    (hasMellin_sub (heat_mellin_convergent _ (by omega) hs)
      ((heat_mellin_convergent (3*m+3) (by omega) hs).const_smul (2 : ℂ))).1
    (heat_mellin_convergent _ (by omega) hs)).1

theorem camera_block_mellin (m : ℕ) {s : ℂ} (hs : 0 < s.re) :
    mellin (cameraHeatBlock m) (s/2) =
      Complex.Gammaℝ s * realCpSaturatedBracket 3 m s := by
  have h := finite_address_mellin 3 ![1,-2,1] ![3*m+2,3*m+3,3*m+4]
    (by intro i; fin_cases i <;> dsimp <;> omega) hs
  rw [realCpSaturatedBracket_three_eq_values]
  change mellin (fun x => heatSample (3*m+2) x - 2*heatSample (3*m+3) x +
    heatSample (3*m+4) x) (s/2) = _
  simpa [Fin.sum_univ_succ, dirichletValue, natDirichletTerm,
    dirichletTerm, sub_eq_add_neg, mul_assoc, add_assoc] using h

theorem camera_prefix_mellin_convergent (M L : ℕ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (cameraHeatPrefix M L) (s/2) := by
  unfold MellinConvergent cameraHeatPrefix
  simp_rw [Finset.smul_sum]
  exact integrable_finsetSum _ (fun k _ => camera_block_mellin_convergent (k+M) hs)

theorem camera_prefix_mellin (M L : ℕ) {s : ℂ} (hs : 0 < s.re) :
    mellin (cameraHeatPrefix M L) (s/2) =
      Complex.Gammaℝ s * ∑ k ∈ Finset.range L, realCpSaturatedBracket 3 (k+M) s := by
  unfold mellin cameraHeatPrefix
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun k _ => camera_block_mellin_convergent (k+M) hs),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact camera_block_mellin (k+M) hs

theorem mellin_heat_bound_integrable (n : ℕ) (hn : 0 < n) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => x^((s/2).re-1)*heat n x) (Ioi 0) := by
  have h := (heat_mellin_convergent n hn hs).norm
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.sub_re, Complex.one_re, heatSample, Complex.norm_real, Real.norm_eq_abs,
    Real.abs_exp, heat]

/-- Dominated convergence of the actual integrals, not merely of their
closed-form Dirichlet evaluations. Cancellation is performed cellwise. -/
theorem camera_prefix_mellin_tendsto (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun L : ℕ => mellin (cameraHeatPrefix M L) (s/2)) atTop
      (𝓝 (mellin (cameraHeatTail M) (s/2))) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x : ℝ => x^((s/2).re-1)*heat (3*M+2) x)
    (fun L => (camera_prefix_mellin_convergent M L hs).aestronglyMeasurable)
    (mellin_heat_bound_integrable _ (by omega) hs)
  · intro L
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left (camera_prefix_norm_le M L hx.le)
      (Real.rpow_nonneg hx.le _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact tendsto_const_nhds.smul (camera_prefix_tendsto M hx)

/-- Calibration of the original stored valueTail by the Mellin integral
of precisely its omitted camera cells, throughout Re(s)>0. -/
theorem camera_tail_mellin (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    mellin (cameraHeatTail M) (s/2) =
      Complex.Gammaℝ s * realCpBracketCutoffTail 3 M s := by
  have hsum := (summable_nat_add_iff M).2
    (summable_realCpSaturatedBracket 3 (by norm_num) (by linarith : -1 < s.re))
  have hlimit := (tendsto_const_nhds (x := Complex.Gammaℝ s)).mul
    hsum.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique (camera_prefix_mellin_tendsto M hs)
    (by simpa only [camera_prefix_mellin M _ hs, realCpBracketCutoffTail] using hlimit)

theorem camera_tail_mellin_convergent (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (cameraHeatTail M) (s/2) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => (x : ℂ)^(s/2-1) • cameraHeatTail M x) (volume.restrict (Ioi 0)) := by
    refine (ContinuousOn.aestronglyMeasurable
      (f := fun x : ℝ => (x : ℂ)^(s/2-1)) ?_ measurableSet_Ioi).smul
      (camera_tail_measurable M)
    exact continuousOn_of_forall_continuousAt fun x hx =>
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt hx))
  apply Integrable.mono' (mellin_heat_bound_integrable (3*M+2) (by omega) hs) hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.sub_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_left (camera_tail_norm_le M hx) (Real.rpow_nonneg hx.le _)

end
end CarryCameraTail
