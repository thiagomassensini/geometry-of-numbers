import C3PowerTail

namespace CarryC3Tail
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets CPFormal.Analytic.Cp
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

theorem height_mem_bracket_half_plane (w : ℂ) (hw : ‖w‖ < (1:ℝ)) :
    operatorHeightParameter w ∈ bracketHalfPlane := by
  have hi := Complex.im_le_norm w
  norm_num [bracketHalfPlane,operatorHeightParameter,Complex.mul_re]
  linarith

/-- Infinite acceleration of the SAME stored value tail. Both endpoints
survive the finite identity; the endpoint at infinity is proved to vanish. -/
theorem native_c3_tail_acceleration (M : ℕ) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    realCpBracketCutoffTail 3 M (operatorHeightParameter w) =
      c3Boundary (fun n => c3Sample n w) (3*M+2)+
        (1/729:ℂ)*∑' k : ℕ, fd 14 (fun n => c3Sample n w) (3*(k+M)+2) := by
  have hs : -1 < (operatorHeightParameter w).re :=
    height_mem_bracket_half_plane w (lt_of_le_of_lt hw (by norm_num))
  have hcell := (summable_norm_realCpSaturatedBracket 3 (by norm_num) hs).comp_injective
    (show Function.Injective (fun k : ℕ => k+M) from fun _ _ h => Nat.add_right_cancel h)
  have hl := hcell.of_norm.hasSum.tendsto_sum_nat
  have hr : Tendsto (fun N : ℕ =>
      c3Boundary (fun n => c3Sample n w) (3*M+2)-
        c3Boundary (fun n => c3Sample n w) (3*M+2+3*N)+
          (1/729:ℂ)*∑ k ∈ Finset.range N,
            fd 14 (fun n => c3Sample n w) (3*(k+M)+2)) atTop
      (nhds (c3Boundary (fun n => c3Sample n w) (3*M+2)+
        (1/729:ℂ)*∑' k : ℕ, fd 14 (fun n => c3Sample n w) (3*(k+M)+2))) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub (c3_boundary_at_infinity M w hw)).add
        ((c3_fourteenth_summable M w hw).of_norm.hasSum.tendsto_sum_nat.const_mul (1/729:ℂ))
  apply tendsto_nhds_unique hl
  exact hr.congr' (.of_forall (fun N => (native_c3_tail_window M N w).symm))

def acceleratedC3Tail (M : ℕ) (w : ℂ) : ℂ :=
  realCpBracketCutoffTail 3 M (operatorHeightParameter w)-
    c3Boundary (fun n => c3Sample n w) (3*M+2)

def acceleratedC3Head (M : ℕ) (w : ℂ) : ℂ :=
  finiteBracketedDirichletChart 3 M (operatorHeightParameter w)+
    c3Boundary (fun n => c3Sample n w) (3*M+2)

/-- Complete original signal, with seed, unchanged. -/
abbrev fullC3Signal (w : ℂ) : ℂ := bracketedDirichletChart 3 (operatorHeightParameter w)

theorem native_c3_head_tail (M : ℕ) (w : ℂ) (hw : ‖w‖ < (1:ℝ)) :
    fullC3Signal w=acceleratedC3Head M w+acceleratedC3Tail M w := by
  rw [fullC3Signal,bracketedDirichletChart_eq_finite_add_cutoffTail 3 M (by norm_num)
    (height_mem_bracket_half_plane w hw)]
  unfold acceleratedC3Head acceleratedC3Tail
  ring

theorem accelerated_c3_tail_bound (M : ℕ) (hM : 0 < M)
    (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖acceleratedC3Tail M w‖ ≤ (Nat.factorial 14:ℝ)/(729*(3*(M:ℝ)-1)^13) := by
  rw [acceleratedC3Tail,native_c3_tail_acceleration M w hw,add_sub_cancel_left,norm_mul]
  norm_num only [norm_div,norm_one,Complex.norm_ofNat]
  calc
    _ ≤ (1/729:ℝ)*((Nat.factorial 14:ℝ)/(3*(M:ℝ)-1)^13) :=
      mul_le_mul_of_nonneg_left (c3_fourteenth_series_bound M hM w hw) (by norm_num)
    _ = (Nat.factorial 14:ℝ)/(729*(3*(M:ℝ)-1)^13) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

theorem c3_boundary_entire (a : ℕ) (ha : 0 < a) :
    Differentiable ℂ (fun w => c3Boundary (fun n => c3Sample n w) a) := by
  have h (n : ℕ) := native_fd_entire n a ha
  have h1 := (h 1).const_mul (-(1/3:ℂ))
  have h2 := h1.add ((h 2).const_mul (1/3:ℂ))
  have h3 := h2.sub ((h 3).const_mul (2/9:ℂ))
  have h4 := h3.add ((h 4).const_mul (1/9:ℂ))
  have h5 := h4.sub ((h 5).const_mul (1/27:ℂ))
  have h7 := h5.add ((h 7).const_mul (1/81:ℂ))
  have h8 := h7.sub ((h 8).const_mul (1/81:ℂ))
  have h9 := h8.add ((h 9).const_mul (2/243:ℂ))
  have h10 := h9.sub ((h 10).const_mul (1/243:ℂ))
  exact h10.add ((h 11).const_mul (1/729:ℂ))

theorem original_c3_tail_analytic (M : ℕ) (w : ℂ) (hw : ‖w‖ < (1:ℝ)) :
    AnalyticAt ℂ (fun u => realCpBracketCutoffTail 3 M (operatorHeightParameter u)) w := by
  have hd : DifferentiableOn ℂ
      (fun u => realCpBracketCutoffTail 3 M (operatorHeightParameter u)) (Metric.ball 0 (1:ℝ)) := by
    intro u hu
    have hp : DifferentiableAt ℂ operatorHeightParameter u := by unfold operatorHeightParameter; fun_prop
    exact (((hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail M
      (height_mem_bracket_half_plane u (by simpa using hu))).differentiableAt).comp u hp).differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))

theorem accelerated_c3_tail_analytic (M : ℕ) (w : ℂ) (hw : ‖w‖ < (1:ℝ)) :
    AnalyticAt ℂ (acceleratedC3Tail M) w :=
  (original_c3_tail_analytic M w hw).sub ((c3_boundary_entire (3*M+2) (by omega)).analyticAt w)

theorem accelerated_c3_head_analytic (M : ℕ) : AnalyticAt ℂ (acceleratedC3Head M) 0 := by
  have hf : Differentiable ℂ (finiteBracketedDirichletChart 3 M) :=
    fun s => (hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet M s).differentiableAt
  have hp : AnalyticAt ℂ operatorHeightParameter 0 := by unfold operatorHeightParameter; fun_prop
  exact ((hf.analyticAt _).comp hp).add ((c3_boundary_entire (3*M+2) (by omega)).analyticAt 0)

def c3TailJetBudget (r M : ℕ) : ℝ :=
  (Nat.factorial 14:ℝ)*2^r/(729*(3*(M:ℝ)-1)^13)

theorem accelerated_c3_tail_jet_bound (r M : ℕ) (hM : 0 < M) :
    ‖sourceJet r (acceleratedC3Tail M)‖ ≤ c3TailJetBudget r M := by
  have hd : DifferentiableOn ℂ (acceleratedC3Tail M) (Metric.ball 0 (1:ℝ)) :=
    fun w hw => (accelerated_c3_tail_analytic M w (by simpa using hw)).differentiableAt.differentiableWithinAt
  have hc : DiffContOnCl ℂ (acceleratedC3Tail M) (Metric.ball 0 (1/2:ℝ)) := by
    apply hd.diffContOnCl_ball
    intro w hw
    have hn : ‖w‖ ≤ (1/2:ℝ) := by simpa using hw
    simpa using (lt_of_le_of_lt hn (by norm_num : (1/2:ℝ)<1))
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c:=(0:ℂ)) (f:=acceleratedC3Tail M) r (by norm_num : (0:ℝ)<1/2) hc
    (fun w hw => accelerated_c3_tail_bound M hM w
      (by
        have he : ‖w‖=(1/2:ℝ) := by simpa using hw
        exact he.le))
  rw [sourceJet,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<r.factorial)).2
  rw [show (1/2:ℝ)^r=(2^r)⁻¹ by rw [one_div,inv_pow],div_inv_eq_mul] at hb
  exact hb.trans_eq (by unfold c3TailJetBudget; ring)

theorem native_c3_signal_jet_error (r M : ℕ) (hM : 0 < M) :
    ‖sourceJet r fullC3Signal-sourceJet r (acceleratedC3Head M)‖ ≤ c3TailJetBudget r M := by
  have he : fullC3Signal =ᶠ[nhds (0:ℂ)]
      (fun w => acceleratedC3Head M w+acceleratedC3Tail M w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (by simp : (0:ℂ) ∈ Metric.ball 0 (1:ℝ))] with w hw
    exact native_c3_head_tail M w (by simpa using hw)
  have hj : sourceJet r fullC3Signal=sourceJet r (acceleratedC3Head M)+sourceJet r (acceleratedC3Tail M) := by
    unfold sourceJet
    rw [he.iteratedDeriv_eq]
    exact sourceJet_add r _ _ (accelerated_c3_head_analytic M) (accelerated_c3_tail_analytic M 0 (by norm_num))
  rw [hj,add_sub_cancel_left]
  exact accelerated_c3_tail_jet_bound r M hM

/-- All seven errors are bounded by a fixed rational number at 64 ORIGINAL
C3 cells. No floating tail approximation is received as an interval. -/
theorem native_c3_seven_jet_error_at64 (r : Fin 7) :
    ‖sourceJet r.val fullC3Signal-sourceJet r.val (acceleratedC3Head 64)‖ ≤ (1/10^19:ℝ) := by
  apply (native_c3_signal_jet_error r.val 64 (by norm_num)).trans
  unfold c3TailJetBudget
  have hp : (2:ℝ)^r.val ≤ 64 := by
    calc
      (2:ℝ)^r.val ≤ (2:ℝ)^6 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by norm_num
  norm_num
  nlinarith

end
end CarryC3Tail
