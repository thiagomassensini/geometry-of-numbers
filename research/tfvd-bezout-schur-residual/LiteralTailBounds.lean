import LiteralTfvd
import Mathlib.Analysis.Normed.Group.Bounded

namespace CarrySourceBezout
open CarrySelfAdjointOperator NativeTrace
open CPFormal.Analytic.Cp Filter Topology
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem literal_height_half_plane (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    operatorHeightParameter w ∈ bracketHalfPlane := by
  have hi := Complex.im_le_norm w
  norm_num [bracketHalfPlane, operatorHeightParameter, Complex.mul_re]
  linarith

theorem literal_cell_bound (m : ℕ) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖realCpSaturatedBracket 3 m (operatorHeightParameter w)‖ ≤
      4/(((m:ℝ)+1)^2) := by
  let s := operatorHeightParameter w
  have hs : 0 ≤ s.re := by
    have hi := Complex.im_le_norm w
    dsimp [s, operatorHeightParameter]
    norm_num [Complex.mul_re]
    linarith
  have hnorm : ‖s‖ ≤ 1 := by
    change ‖(1/2:ℂ)+Complex.I*w‖ ≤ 1
    have hh := norm_add_le (1/2:ℂ) (Complex.I*w)
    norm_num [norm_mul] at hh
    linarith
  have hconst : cpBracketMajorantConstant 3 s ≤ 4 := by
    have hn : ‖s*(s+1)‖ ≤ 2 := by
      rw [norm_mul]
      have hp : ‖s+1‖ ≤ 2 := by
        have hh := norm_add_le s 1
        rw [norm_one] at hh
        linarith
      exact (mul_le_mul hnorm hp (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
    norm_num only [cpBracketMajorantConstant, CPFormal.Genuine.Cp.halfRange,
      Nat.reduceSub, Nat.reduceDiv, Finset.Icc_self, Finset.sum_singleton,
      Nat.cast_one, one_pow, mul_one]
    linarith
  have hp : ((m:ℝ)+1)^(-s.re-2) ≤ 1/((m:ℝ)+1)^2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ (m:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) m])
      (show -s.re-2 ≤ (-2:ℝ) by linarith)
    convert hh using 1
    rw [Real.rpow_neg (by positivity), show (2:ℝ)=(2:ℕ) by norm_num,
      Real.rpow_natCast, one_div]
  have hb := norm_realCpSaturatedBracket_le (p:=3) (k:=m) (by norm_num)
    (show -1 < s.re by linarith)
  push_cast at hb
  exact hb.trans ((mul_le_mul hconst hp (by positivity) (by norm_num)).trans_eq (by ring))

/-- Original C3 lattice, all omitted cells, no accelerated replacement. -/
theorem literal_c3_tail_bound (M : ℕ) (w : ℂ) (hw : ‖w‖ ≤ (1/2:ℝ)) :
    ‖realCpBracketCutoffTail 3 M (operatorHeightParameter w)‖ ≤ 8/((M:ℝ)+1) := by
  have hs := (summable_norm_realCpSaturatedBracket 3 (by norm_num)
    (literal_height_half_plane w hw)).comp_injective
      (show Function.Injective (fun k : ℕ => k+M) from fun _ _ h => Nat.add_right_cancel h)
  have step (m : ℕ) : (4:ℝ)/((m:ℝ)+1)^2 ≤
      8/((m:ℝ)+1)-8/((m:ℝ)+2) := by
    have he : 8/((m:ℝ)+1)-8/((m:ℝ)+2) =
        8/(((m:ℝ)+1)*((m:ℝ)+2)) := by field_simp; ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  have env : ∀ N : ℕ, (∑ k ∈ Finset.range N,
      (4:ℝ)/(((k:ℝ)+M+1)^2)) ≤
        8/((M:ℝ)+1)-8/((N:ℝ)+M+1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hh := step (N+M)
      push_cast at ih hh ⊢
      rw [show (N:ℝ)+1+M+1 = (N:ℝ)+M+2 by ring]
      linarith
  have total : ∑' k : ℕ, ‖realCpSaturatedBracket 3 (k+M) (operatorHeightParameter w)‖ ≤
      8/((M:ℝ)+1) := by
    apply tsum_le_of_sum_le' (by positivity)
    intro s
    obtain ⟨N,hN⟩ := Finset.exists_nat_subset_range s
    calc
      _ ≤ ∑ k ∈ Finset.range N, ‖realCpSaturatedBracket 3 (k+M) (operatorHeightParameter w)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _ => norm_nonneg _)
      _ ≤ ∑ k ∈ Finset.range N, (4:ℝ)/(((k:ℝ)+M+1)^2) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [Nat.cast_add] using literal_cell_bound (k+M) w hw
      _ ≤ _ := (env N).trans (sub_le_self _ (by positivity))
  exact (norm_tsum_le_tsum_norm hs).trans total

theorem literal_multiplier_analytic_at (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) :
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

theorem literal_original_tail_analytic (M : ℕ) (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) :
    AnalyticAt ℂ (fun u => realCpBracketCutoffTail 3 M (operatorHeightParameter u)) w := by
  have hd : DifferentiableOn ℂ
      (fun u => realCpBracketCutoffTail 3 M (operatorHeightParameter u)) (Metric.ball 0 (1/2:ℝ)) := by
    intro u hu
    have hp : DifferentiableAt ℂ operatorHeightParameter u := by unfold operatorHeightParameter; fun_prop
    have hs := literal_height_half_plane u
      (le_of_lt (show ‖u‖ < (1/2:ℝ) by simpa using hu))
    have ht := (hasDerivAt_realCpBracketCutoffTail_eq_neg_logJetTail M hs).differentiableAt
    exact (ht.comp u hp).differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))

theorem literal_tail_value_formula (M : ℕ) (w : ℂ) :
    (tailTrace M w).1 = valueMultiplier w * realCpBracketCutoffTail 3 M (operatorHeightParameter w) := by
  unfold tailTrace tracePiece canonicalC3BracketTfvdCompletionState valueMultiplier
  dsimp
  ring

theorem literal_head_analytic_at (M : ℕ) (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) :
    AnalyticAt ℂ (fun z => (headTrace M z).1) w := by
  have hf : Differentiable ℂ (finiteBracketedDirichletChart 3 M) :=
    fun s => (hasDerivAt_finiteBracketedDirichletChart_three_eq_neg_logJet M s).differentiableAt
  have hp : AnalyticAt ℂ operatorHeightParameter w := by unfold operatorHeightParameter; fun_prop
  exact ((literal_multiplier_analytic_at w hw).mul ((hf.analyticAt _).comp hp)).congr
    (.of_forall (fun z => (head_value_formula M z).symm))

theorem literal_tail_analytic_at (M : ℕ) (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) :
    AnalyticAt ℂ (fun z => (tailTrace M z).1) w :=
  ((literal_multiplier_analytic_at w hw).mul
    (literal_original_tail_analytic M w hw)).congr
      (.of_forall (fun z => (literal_tail_value_formula M z).symm))

/-- Cauchy bound on the same fixed disk, without importing numeric evaluators. -/
theorem literal_cauchy_quarter (f : ℂ → ℂ) (C : ℝ)
    (ha : ∀ w, ‖w‖ ≤ (1/4:ℝ) → AnalyticAt ℂ f w)
    (hb : ∀ w, ‖w‖ ≤ (1/4:ℝ) → ‖f w‖ ≤ C) (r : ℕ) :
    ‖sourceJet r f‖ ≤ C*4^r := by
  have hd : DiffContOnCl ℂ f (Metric.ball 0 (1/4:ℝ)) := by
    apply (show DifferentiableOn ℂ f (Metric.closedBall 0 (1/4:ℝ)) from
      fun w hw => (ha w (by simpa using hw)).differentiableAt.differentiableWithinAt).diffContOnCl_ball
    exact Set.Subset.rfl
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c:=(0:ℂ)) (f:=f) r
    (by norm_num : (0:ℝ)<1/4) hd (fun w hw => hb w
      (by have he : ‖w‖=(1/4:ℝ) := by simpa using hw
          exact he.le))
  rw [sourceJet,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<r.factorial)).2
  rw [show (1/4:ℝ)^r=(4^r)⁻¹ by rw [one_div,inv_pow],div_inv_eq_mul] at hh
  exact hh.trans_eq (by ring)

/-- The constant is derived from continuity of the original completion on
+a compact disk. It is not a metric, moment normalization, or sign input. -/
theorem literal_tail_jet_envelope : ∃ C : ℝ, 0 < C ∧ ∀ M n : ℕ,
    ‖literalTail M n‖ ≤ (C/((M:ℝ)+1))*16^n := by
  have hc : ContinuousOn valueMultiplier (Metric.closedBall 0 (1/4:ℝ)) := by
    intro w hw
    exact (literal_multiplier_analytic_at w (lt_of_le_of_lt
      (show ‖w‖ ≤ (1/4:ℝ) by simpa using hw) (by norm_num))).continuousAt.continuousWithinAt
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0:ℂ) (1/4:ℝ)).exists_bound_of_continuousOn hc
  let K : ℝ := max A 1
  have hK : 0 < K := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  refine ⟨8*K, by positivity, ?_⟩
  intro M n
  have he := literal_cauchy_quarter (fun z => (tailTrace M z).1) (8*K/((M:ℝ)+1))
    (fun w hw => literal_tail_analytic_at M w (hw.trans_lt (by norm_num)))
    (fun w hw => by
      rw [literal_tail_value_formula, norm_mul]
      have hb : ‖valueMultiplier w‖ ≤ K := (hA w (by simpa using hw)).trans (le_max_left _ _)
      have hh := mul_le_mul hb (literal_c3_tail_bound M w (hw.trans (by norm_num)))
        (norm_nonneg _) hK.le
      exact hh.trans_eq (by ring)) (2*n)
  simpa [literalTail, pow_mul, show (4:ℝ)^2=16 by norm_num] using he

end
end CarrySourceBezout
