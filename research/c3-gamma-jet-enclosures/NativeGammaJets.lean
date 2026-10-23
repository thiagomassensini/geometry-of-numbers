import FiniteGamma

namespace CarryC3Gamma
open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets
open Set Filter Topology
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
set_option exponentiation.threshold 1024

theorem exp_neg_eighty_one_bound : Real.exp (-81) ≤ 1/10^33 := by
  have he : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp : (8/3:ℝ)^81 ≤ (Real.exp 1)^81 := pow_le_pow_left₀ (by norm_num) he 81
  rw [show (-81:ℝ)=-((81:ℕ)*(1:ℝ)) by norm_num,Real.exp_neg,Real.exp_nat_mul]
  calc
    ((Real.exp 1)^81)⁻¹ ≤ ((8/3:ℝ)^81)⁻¹ :=
      by simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<(8/3)^81) hp
    _ ≤ 1/10^33 := by norm_num

/-- Explicit uniform accuracy on a strip containing the actual Gamma argument. -/
theorem gamma_finite_512_error (z : ℂ) (hz : (1/8:ℝ) ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖Complex.Gamma z-gammaFinite 512 81 z‖ ≤ 1/10^32 := by
  apply (gamma_finite_error 512 81 (by norm_num) (by norm_num) z
    (by linarith) hz1).trans
  have h : 2*(81:ℝ)^(512+1)/((Nat.factorial 512:ℝ)*z.re) ≤
      16*(81:ℝ)^513/(Nat.factorial 512:ℝ) := by
    calc
      _ ≤ 2*(81:ℝ)^(512+1)/((Nat.factorial 512:ℝ)*(1/8)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      _ = _ := by norm_num1
  have hr : 16*(81:ℝ)^513/(Nat.factorial 512:ℝ) ≤ 1/10^100 := by norm_num1
  have hs := add_le_add (h.trans hr) exp_neg_eighty_one_bound
  exact hs.trans (by norm_num1)

/-- The SAME Gamma argument in the native Xi completion. -/
def nativeGamma (w : ℂ) : ℂ := Complex.Gamma (operatorHeightParameter w/2)
def finiteNativeGamma (w : ℂ) : ℂ := gammaFinite 512 81 (operatorHeightParameter w/2)

theorem native_gamma_argument (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    (1/8:ℝ) ≤ (operatorHeightParameter w/2).re ∧
      (operatorHeightParameter w/2).re ≤ 3/8 := by
  have hi := Complex.abs_im_le_norm w
  norm_num [operatorHeightParameter,Complex.div_re,Complex.mul_re]
  constructor <;> linarith [le_abs_self w.im,neg_abs_le w.im]

theorem native_gamma_uniform_error (w : ℂ) (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖nativeGamma w-finiteNativeGamma w‖ ≤ 1/10^32 := by
  obtain ⟨hl,hu⟩ := native_gamma_argument w hw
  exact gamma_finite_512_error _ hl (by linarith)

theorem finite_gamma_analytic (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) :
    AnalyticAt ℂ finiteNativeGamma w := by
  have hz : 0 < (operatorHeightParameter w/2).re := by
    have hi := Complex.im_le_norm w
    norm_num [operatorHeightParameter,Complex.div_re,Complex.mul_re]
    linarith
  have harg : AnalyticAt ℂ (fun w => operatorHeightParameter w/2) w := by
    unfold operatorHeightParameter
    fun_prop
  unfold finiteNativeGamma gammaFinite
  apply AnalyticAt.mul
  · change AnalyticAt ℂ (fun w => (81:ℂ)^(operatorHeightParameter w/2)) w
    simp only [Complex.cpow_def_of_ne_zero (by norm_num : (81:ℂ) ≠ 0)]
    exact (analyticAt_const.mul harg).cexp
  · apply Finset.analyticAt_fun_sum
    intro k hk
    apply AnalyticAt.div analyticAt_const (analyticAt_const.mul (harg.add analyticAt_const))
    apply mul_ne_zero
    · change (k.factorial:ℂ) ≠ 0
      exact_mod_cast Nat.factorial_ne_zero k
    intro he
    have hr := congrArg Complex.re he
    change (operatorHeightParameter w/2+(k:ℂ)).re=0 at hr
    simp only [Complex.add_re,Complex.natCast_re] at hr
    linarith [Nat.cast_nonneg (α:=ℝ) k]

theorem native_gamma_analytic (w : ℂ) (hw : ‖w‖ < (1/2:ℝ)) :
    AnalyticAt ℂ nativeGamma w := by
  have hd : DifferentiableOn ℂ nativeGamma (Metric.ball 0 (1/2:ℝ)) := by
    intro v hv
    have hvn : ‖v‖ < (1/2:ℝ) := by simpa using hv
    have hz : 0 < (operatorHeightParameter v/2).re := by
      have hi := Complex.im_le_norm v
      norm_num [operatorHeightParameter,Complex.div_re,Complex.mul_re]
      linarith
    have he : DifferentiableAt ℂ (fun w => operatorHeightParameter w/2) v := by
      unfold operatorHeightParameter
      fun_prop
    exact (((Complex.differentiableAt_Gamma _ (fun m hm => by
      have hh := congrArg Complex.re hm
      simp only [Complex.neg_re,Complex.natCast_re] at hh
      linarith [Nat.cast_nonneg (α:=ℝ) m])).comp v he)).differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hw))

/-- Error in every factorial-normalized jet of the original Gamma factor. -/
theorem native_gamma_jet_error (r : ℕ) :
    ‖sourceJet r nativeGamma-sourceJet r finiteNativeGamma‖ ≤ 4^r/10^32 := by
  have ha : DifferentiableOn ℂ (fun w => nativeGamma w-finiteNativeGamma w)
      (Metric.ball 0 (1/2:ℝ)) := by
    intro w hw
    have hn : ‖w‖ < (1/2:ℝ) := by simpa using hw
    exact ((native_gamma_analytic w hn).sub (finite_gamma_analytic w hn)).differentiableAt.differentiableWithinAt
  have hd : DiffContOnCl ℂ (fun w => nativeGamma w-finiteNativeGamma w)
      (Metric.ball 0 (1/4:ℝ)) := by
    apply ha.diffContOnCl_ball
    intro w hw
    have hn : ‖w‖ ≤ (1/4:ℝ) := by simpa using hw
    simpa using (lt_of_le_of_lt hn (by norm_num : (1/4:ℝ)<1/2))
  have hb := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (c:=(0:ℂ)) (f:=fun w => nativeGamma w-finiteNativeGamma w) r
    (by norm_num : (0:ℝ)<1/4) hd (by
      intro w hw
      exact native_gamma_uniform_error w (by
        have he : ‖w‖ = (1/4:ℝ) := by simpa using hw
        exact he.le))
  have he : sourceJet r nativeGamma-sourceJet r finiteNativeGamma =
      sourceJet r (fun w => nativeGamma w-finiteNativeGamma w) := by
    unfold sourceJet
    change _ = iteratedDeriv r (nativeGamma-finiteNativeGamma) 0/(r.factorial:ℂ)
    rw [iteratedDeriv_sub (native_gamma_analytic 0 (by norm_num)).contDiffAt
      (finite_gamma_analytic 0 (by norm_num)).contDiffAt,sub_div]
  rw [he,sourceJet,norm_div,Complex.norm_natCast]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<r.factorial)).2
  have hr : (1/4:ℝ)^r = (4^r)⁻¹ := by rw [one_div,inv_pow]
  rw [hr,div_inv_eq_mul] at hb
  exact hb.trans_eq (by ring)

end
end CarryC3Gamma
