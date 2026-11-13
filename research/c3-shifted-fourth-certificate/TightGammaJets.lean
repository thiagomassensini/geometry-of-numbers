import NativeGammaJets

namespace CarryC3Gamma

open CarrySelfAdjointOperator PhysicalSewing CarryTwoEvenJets
open Set Filter Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 7000
set_option exponentiation.threshold 1024

/-- The original exponential remainder at 81 is smaller than `10⁻³⁴`.
This refines the coarser bound in the general Gamma ledger without changing
its cutoff, source, or scaling. -/
theorem exp_neg_eighty_one_bound_tight : Real.exp (-81) ≤ 1/10^34 := by
  have he : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp : (8/3:ℝ)^81 ≤ (Real.exp 1)^81 := pow_le_pow_left₀ (by norm_num) he 81
  rw [show (-81:ℝ)=-((81:ℕ)*(1:ℝ)) by norm_num,
    Real.exp_neg, Real.exp_nat_mul]
  calc
    ((Real.exp 1)^81)⁻¹ ≤ ((8/3:ℝ)^81)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (by norm_num : (0:ℝ)<(8/3)^81) hp
    _ ≤ 1/10^34 := by norm_num

/-- The same finite Gamma approximation as the original ledger, with a tighter
uniform remainder obtained only by sharpening its explicit `exp (-81)` term. -/
theorem gamma_finite_512_error_tight (z : ℂ)
    (hz : (1/8:ℝ) ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖Complex.Gamma z-gammaFinite 512 81 z‖ ≤ 2/10^34 := by
  apply (gamma_finite_error 512 81 (by norm_num) (by norm_num) z
    (by linarith) hz1).trans
  have h : 2*(81:ℝ)^(512+1)/((Nat.factorial 512:ℝ)*z.re) ≤
      16*(81:ℝ)^513/(Nat.factorial 512:ℝ) := by
    calc
      _ ≤ 2*(81:ℝ)^(512+1)/((Nat.factorial 512:ℝ)*(1/8)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
      _ = _ := by norm_num1
  have hr : 16*(81:ℝ)^513/(Nat.factorial 512:ℝ) ≤ 1/10^100 := by norm_num1
  have hs := add_le_add (h.trans hr) exp_neg_eighty_one_bound_tight
  exact hs.trans (by norm_num1)

theorem native_gamma_uniform_error_tight (w : ℂ)
    (hw : ‖w‖ ≤ (1/4:ℝ)) :
    ‖nativeGamma w-finiteNativeGamma w‖ ≤ 2/10^34 := by
  obtain ⟨hl,hu⟩ := native_gamma_argument w hw
  exact gamma_finite_512_error_tight _ hl (by linarith)

/-- Tighter factorial-normalized jet error, derived from the same original
Gamma approximation and Cauchy circle used by `native_gamma_jet_error`. -/
theorem native_gamma_jet_error_tight (r : ℕ) :
    ‖sourceJet r nativeGamma-sourceJet r finiteNativeGamma‖ ≤
      2*4^r/10^34 := by
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
      exact native_gamma_uniform_error_tight w (by
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

#print axioms exp_neg_eighty_one_bound_tight
#print axioms gamma_finite_512_error_tight
#print axioms native_gamma_jet_error_tight

end
end CarryC3Gamma
