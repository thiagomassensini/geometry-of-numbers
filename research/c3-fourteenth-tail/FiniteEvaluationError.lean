import C3FiniteCoefficients

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CarryC3Gamma CPFormal.Analytic.Cp
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem characteristic_c3_formula (w : ℂ) :
    completedNativeOperatorCharacteristic w=valueMultiplier w*fullC3Signal w := by
  rw [completedNativeOperatorCharacteristic,nativeScalar_eq_genuineContinuation_unconditional]
  unfold genuineContinuation cpGenuineQuotient valueMultiplier fullC3Signal
  ring

theorem value_multiplier_analytic_at (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) :
    AnalyticAt ℂ valueMultiplier w := by
  have hd : DifferentiableOn ℂ valueMultiplier (Metric.ball 0 (1/2:ℝ)) := by
    intro v hv
    have hn : ‖v‖ < (1/2:ℝ) := by simpa using hv
    have hs : operatorHeightParameter v ∈ genuineCriticalStrip := by
      have hi := Complex.abs_im_le_norm v
      norm_num [genuineCriticalStrip,operatorHeightParameter,Complex.mul_re]
      constructor <;> linarith [le_abs_self v.im,neg_abs_le v.im]
    have hp : DifferentiableAt ℂ operatorHeightParameter v := by unfold operatorHeightParameter; fun_prop
    have hc : DifferentiableAt ℂ (fun w => cpChartFactor 3 (operatorHeightParameter w)) v := by
      unfold cpChartFactor
      fun_prop
    exact ((nativeXiCompletionFactor_differentiableAt hs).div hc
      (canonicalC3ChartFactorHeight_ne_zero hs)).differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))

theorem elementary_multiplier_analytic_at (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) :
    AnalyticAt ℂ c3ElementaryMultiplier w := by
  have harg : 0 < (operatorHeightParameter w/2).re := by
    have hi := Complex.im_le_norm w
    norm_num [operatorHeightParameter,Complex.mul_re,Complex.div_re]
    linarith
  have hg : nativeGamma w≠0 := Complex.Gamma_ne_zero_of_re_pos harg
  have hident : c3ElementaryMultiplier =ᶠ[nhds w] (fun v => valueMultiplier v/nativeGamma v) := by
    filter_upwards [(native_gamma_analytic w hw).continuousAt.eventually_ne hg] with v hv
    rw [c3_value_multiplier_gamma_factorization]
    exact (mul_div_cancel_right₀ _ hv).symm
  exact ((value_multiplier_analytic_at w hw).div (native_gamma_analytic w hw) hg).congr hident.symm

def finiteLeft (w : ℂ) : ℂ := c3ElementaryMultiplier w*acceleratedC3Head 64 w

theorem finite_left_analytic : AnalyticAt ℂ finiteLeft 0 :=
  (elementary_multiplier_analytic_at 0 (by norm_num)).mul (accelerated_c3_head_analytic 64)

theorem cauchy_quarter (f : ℂ → ℂ) (C : ℝ)
    (ha : ∀ w, ‖w‖ ≤ (1/4:ℝ) → AnalyticAt ℂ f w)
    (hb : ∀ w, ‖w‖ ≤ (1/4:ℝ) → ‖f w‖ ≤ C) (r : ℕ) :
    ‖sourceJet r f‖ ≤ C*4^r := by
  have hd : DiffContOnCl ℂ f (Metric.ball 0 (1/4:ℝ)) := by
    apply (show DifferentiableOn ℂ f (Metric.closedBall 0 (1/4:ℝ)) from
      fun w hw => (ha w (by simpa using hw)).differentiableAt.differentiableWithinAt).diffContOnCl_ball
    exact Subset.rfl
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c:=(0:ℂ)) (f:=f) r
    (by norm_num : (0:ℝ)<1/4) hd (fun w hw => hb w
      (by have he : ‖w‖=(1/4:ℝ) := by simpa using hw
          exact he.le))
  rw [sourceJet,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<r.factorial)).2
  rw [show (1/4:ℝ)^r=(4^r)⁻¹ by rw [one_div,inv_pow],div_inv_eq_mul] at hh
  exact hh.trans_eq (by ring)

theorem finite_left_jet_bound (r : ℕ) : ‖sourceJet r finiteLeft‖ ≤ 64*4^r := by
  apply cauchy_quarter
  · intro w hw
    have ha : AnalyticAt ℂ (acceleratedC3Head 64) w := by
      have hf : Differentiable ℂ (finiteBracketedDirichletChart 3 64) :=
        fun s => (hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet 64 s).differentiableAt
      have hp : AnalyticAt ℂ operatorHeightParameter w := by unfold operatorHeightParameter; fun_prop
      exact ((hf.analyticAt _).comp hp).add ((c3_boundary_entire _ (by omega)).analyticAt w)
    exact (elementary_multiplier_analytic_at w (lt_of_le_of_lt hw (by norm_num))).mul ha
  · intro w hw
    rw [finiteLeft,norm_mul]
    have hh := mul_le_mul (c3_elementary_bound w hw)
      (c3_accelerated_head_at64_bound w (hw.trans (by norm_num))) (norm_nonneg _) (by norm_num : (0:ℝ)≤12)
    exact hh.trans (by norm_num)

def completedTailError (w : ℂ) : ℂ := valueMultiplier w*acceleratedC3Tail 64 w
def completedHead64 (w : ℂ) : ℂ := finiteLeft w*nativeGamma w

theorem completed_head_tail (w : ℂ) (hw : ‖w‖ < (1:ℝ)) :
    completedNativeOperatorCharacteristic w=completedHead64 w+completedTailError w := by
  rw [characteristic_c3_formula,native_c3_head_tail 64 w hw,
    c3_value_multiplier_gamma_factorization]
  unfold completedHead64 finiteLeft completedTailError c3ElementaryMultiplier
  rw [c3_value_multiplier_gamma_factorization]
  ring

theorem completed_tail_jet_error (r : ℕ) :
    ‖sourceJet r completedTailError‖ ≤
      (96*(Nat.factorial 14:ℝ)/(729*191^13))*4^r := by
  apply cauchy_quarter
  · intro w hw
    exact (value_multiplier_analytic_at w (lt_of_le_of_lt hw (by norm_num))).mul
      (accelerated_c3_tail_analytic 64 w (lt_of_le_of_lt hw (by norm_num)))
  · intro w hw
    rw [completedTailError,norm_mul]
    have hh := mul_le_mul (c3_value_multiplier_bound w hw)
      (accelerated_c3_tail_bound 64 (by norm_num) w (hw.trans (by norm_num)))
      (norm_nonneg _) (by norm_num : (0:ℝ)≤96)
    norm_num only [Nat.cast_ofNat] at hh
    exact hh.trans_eq (by ring)

def finiteCompletedJet (r : Fin 7) : ℂ :=
  ∑ j ∈ Finset.range (r.val+1), sourceJet j finiteLeft*gammaReference ⟨r.val-j,by omega⟩

theorem gamma_jet_replacement_error (r : Fin 7) :
    ‖sourceJet r.val completedHead64-finiteCompletedJet r‖ ≤
      (64*(∑ j ∈ Finset.range (r.val+1), (4:ℝ)^j))/10^18 := by
  change ‖sourceJet r.val (fun w => finiteLeft w*nativeGamma w)-finiteCompletedJet r‖ ≤ _
  rw [jet_mul finite_left_analytic (native_gamma_analytic 0 (by norm_num)),finiteCompletedJet,
    ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_sub,norm_mul]
  have hg := native_gamma_seven_boxes ⟨r.val-j,by omega⟩
  have hl := finite_left_jet_bound j
  exact (mul_le_mul hl hg (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem completed_jet_evaluator_error (r : Fin 7) :
    ‖sourceJet r.val completedNativeOperatorCharacteristic-finiteCompletedJet r‖ ≤ (4/10^13:ℝ) := by
  have he : completedNativeOperatorCharacteristic =ᶠ[nhds (0:ℂ)]
      (fun w => completedHead64 w+completedTailError w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simp : (0:ℂ)∈Metric.ball 0 (1:ℝ))] with w hw
    exact completed_head_tail w (by simpa using hw)
  have ha : AnalyticAt ℂ completedTailError 0 :=
    (value_multiplier_analytic_at 0 (by norm_num)).mul (accelerated_c3_tail_analytic 64 0 (by norm_num))
  have hj : sourceJet r.val completedNativeOperatorCharacteristic=
      sourceJet r.val completedHead64+sourceJet r.val completedTailError := by
    unfold sourceJet
    rw [he.iteratedDeriv_eq]
    exact sourceJet_add _ _ _ (finite_left_analytic.mul (native_gamma_analytic 0 (by norm_num))) ha
  rw [hj,show sourceJet r.val completedHead64+sourceJet r.val completedTailError-finiteCompletedJet r=
      (sourceJet r.val completedHead64-finiteCompletedJet r)+sourceJet r.val completedTailError by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add (gamma_jet_replacement_error r) (completed_tail_jet_error r.val)).trans
  fin_cases r <;> norm_num [Finset.sum_range_succ]

end
end CarryC3Tail
