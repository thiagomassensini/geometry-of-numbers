import CriticalBudgetData
import FiniteNormBudget

namespace CarryEffectiveRadial
open CarrySelfAdjointOperator CarryMaterialVariation CarryBoundaryReconstruction CarryMovingRadial
open NativeLaguerre Filter Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000

def criticalCurve (h : ℝ) : ℝ := sixLimit sixU sixV+sixCorrection sixU sixV*h^2+
  h^4*(sixEffectiveRemainder sixU sixV (h:ℂ)).re

theorem critical_curve_hasDerivAt (h : ℝ) (hh : |h|<1/12) :
    HasDerivAt criticalCurve (h*(2*sixCorrection sixU sixV+
      4*h^2*(sixEffectiveRemainder sixU sixV (h:ℂ)).re+
      h^3*(deriv (sixEffectiveRemainder sixU sixV) (h:ℂ)).re)) h := by
  have ha := six_effective_remainder_analytic sixU sixV (h:ℂ) (by simpa using hh)
  have hr := ha.differentiableAt.hasDerivAt.real_of_complex
  have hd := (hasDerivAt_const h (sixLimit sixU sixV)).add
    (((hasDerivAt_id h).pow 2).const_mul (sixCorrection sixU sixV)) |>.add
      (((hasDerivAt_id h).pow 4).mul hr)
  convert hd using 1
  all_goals try rfl
  all_goals (simp [Pi.pow_apply]; ring)

theorem critical_curve_derivative_budget (h : ℝ) (hh : 0<h) (hH : h≤budgetStep) :
    |deriv criticalCurve h|≤2*h := by
  have hH0 : 0<budgetStep := budget_step_positive
  have hsmall : h<1/1000 := lt_of_le_of_lt hH budget_step_small
  have hr := six_effective_remainder_bound sixU sixV (h:ℂ) critical_sizes.1 critical_sizes.2.1
    (by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]; linarith)
  have hrd := six_effective_remainder_deriv_bound sixU sixV (h:ℂ) critical_sizes.1 critical_sizes.2.1
    (by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]; exact hsmall.le)
  have hR := (Complex.abs_re_le_norm (sixEffectiveRemainder sixU sixV (h:ℂ))).trans hr
  have hdR := (Complex.abs_re_le_norm (deriv (sixEffectiveRemainder sixU sixV) (h:ℂ))).trans hrd
  have hC := critical_sizes.2.2
  have hs : |2*sixCorrection sixU sixV+4*h^2*(sixEffectiveRemainder sixU sixV (h:ℂ)).re+
      h^3*(deriv (sixEffectiveRemainder sixU sixV) (h:ℂ)).re|≤
      2*|sixCorrection sixU sixV|+4*h^2*|(sixEffectiveRemainder sixU sixV (h:ℂ)).re|+
        h^3*|(deriv (sixEffectiveRemainder sixU sixV) (h:ℂ)).re| := by
    have ht := (abs_add_le (2*sixCorrection sixU sixV+4*h^2*(sixEffectiveRemainder sixU sixV (h:ℂ)).re)
      (h^3*(deriv (sixEffectiveRemainder sixU sixV) (h:ℂ)).re)).trans
      (add_le_add (abs_add_le (2*sixCorrection sixU sixV)
        (4*h^2*(sixEffectiveRemainder sixU sixV (h:ℂ)).re)) le_rfl)
    simpa [abs_mul,abs_pow,abs_of_pos hh] using ht
  have he : 2*|sixCorrection sixU sixV|+4*h^2*|(sixEffectiveRemainder sixU sixV (h:ℂ)).re|+
      h^3*|(deriv (sixEffectiveRemainder sixU sixV) (h:ℂ)).re|≤
      2*(1/1000:ℝ)+4*budgetStep^2*(10:ℝ)^20+budgetStep^3*(10:ℝ)^22 := by
    gcongr
  have hb : 2*(1/1000:ℝ)+4*budgetStep^2*(10:ℝ)^20+budgetStep^3*(10:ℝ)^22≤2 := by
    norm_num [budgetStep]
  rw [(critical_curve_hasDerivAt h (by rw [abs_of_pos hh]; linarith)).deriv,abs_mul,abs_of_pos hh]
  simpa only [mul_comm h 2] using mul_le_mul_of_nonneg_left (hs.trans (he.trans hb)) hh.le

theorem critical_curve_grid (k : ℕ) (hk : radialFourSourceStep k<1/24) :
    sixPhysical k=criticalCurve (radialFourSourceStep k) := by
  rw [six_physical_at_explicit_step k hk,canonicalGreenJetStep_eq_radialFourSourceStep]
  have hp := radial_step_positive k
  have hf (j : Fin 6) : completedNativeOperatorCharacteristic
      (Complex.I*((j:ℂ)+1)*(radialFourSourceStep k:ℂ))≠0 := by
    exact (six_radial_regular _ (by rwa [abs_of_pos hp]) j).1
  rw [six_expansion_on_disc sixU sixV (radialFourSourceStep k:ℂ)
    (by simpa [abs_of_pos hp] using hk) (by exact_mod_cast hp.ne') hf]
  simp only [criticalCurve,← Complex.ofReal_pow,Complex.add_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem step_at_budget_index : radialFourSourceStep budgetIndex=budgetStep := by
  norm_num [radialFourSourceStep,budgetIndex,budgetStep]

theorem step_after_budget_index (k : ℕ) (hk : budgetIndex≤k) : radialFourSourceStep k≤budgetStep := by
  have hn : (10:ℝ)^20≤(k:ℝ)+1 := by
    exact_mod_cast (show (10:ℕ)^20≤k+1 by unfold budgetIndex at hk; omega)
  unfold radialFourSourceStep budgetStep
  rw [one_div]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hn

/-- Effective budget on ALL later increments of the ORIGINAL full source.
The cutoff is explicit; no limiting pivot sign is an input. -/
theorem six_effective_increment_budget (k : ℕ) (hk : budgetIndex≤k) :
    |sixPhysical k-sixPhysical (k+1)|≤(radialFourSourceStep k)^2-(radialFourSourceStep (k+1))^2 := by
  have ha := step_after_budget_index k hk
  have hb := (radial_step_decreasing k).le.trans ha
  have has : radialFourSourceStep k<1/24 := lt_of_le_of_lt ha (by norm_num [budgetStep])
  have hbs : radialFourSourceStep (k+1)<1/24 := lt_of_le_of_lt hb (by norm_num [budgetStep])
  rw [critical_curve_grid k has,critical_curve_grid (k+1) hbs]
  apply squared_step_budget criticalCurve _ _ (radial_step_decreasing k).le
  · intro x hx
    apply (critical_curve_hasDerivAt x ?_).differentiableAt
    have hxp : 0<x := lt_of_lt_of_le (radial_step_positive _) hx.1
    rw [abs_of_pos hxp]
    exact lt_of_le_of_lt (hx.2.trans ha) (by norm_num [budgetStep])
  · intro x hx
    exact critical_curve_derivative_budget x (lt_of_lt_of_le (radial_step_positive _) hx.1) (hx.2.trans ha)

/-- Actual finite-scale source enclosure, with the ENTIRE analytic tail. -/
theorem six_effective_anchor_positive : (1/(10:ℝ)^16)<sixPhysical budgetIndex := by
  rw [critical_curve_grid budgetIndex (by rw [step_at_budget_index]; norm_num [budgetStep]),step_at_budget_index]
  have hR := six_effective_remainder_bound sixU sixV (budgetStep:ℂ) critical_sizes.1 critical_sizes.2.1
    (by norm_num [budgetStep])
  have hRe := (abs_le.mp ((Complex.abs_re_le_norm _).trans hR)).1
  have hb := mul_le_mul_of_nonneg_left hRe (pow_nonneg budget_step_positive.le 4)
  have hh := anchor_head_lower
  have hc : (1/(10:ℝ)^16)<15/(10:ℝ)^17-budgetStep^4*(10:ℝ)^20 := by norm_num [budgetStep]
  unfold criticalCurve
  linarith

/-- Finite test closes via the original anchor and effective increment
budget, without consuming an earlier canonical pivot positivity theorem. -/
theorem six_boundary_positive_from_effective_budget : 0<sixLimit sixU sixV := by
  apply CarryBoundaryReconstruction.positive_boundary_of_increment_budget sixPhysical _ 1
    six_physical_tendsto (by norm_num) budgetIndex
  · intro j
    simpa only [one_mul] using six_effective_increment_budget (budgetIndex+j) (by omega)
  · rw [step_at_budget_index,one_mul]
    exact lt_trans (by norm_num [budgetStep] : budgetStep^2<1/(10:ℝ)^16) six_effective_anchor_positive

theorem six_effective_absolute_tail (K : ℕ) (hK : budgetIndex≤K) :
    HasSum (fun j => sixPhysical (K+j)-sixPhysical (K+j+1))
      (sixPhysical K-sixLimit sixU sixV) ∧
    Summable (fun j => |sixPhysical (K+j)-sixPhysical (K+j+1)|) ∧
    (∑' j, |sixPhysical (K+j)-sixPhysical (K+j+1)|)≤(radialFourSourceStep K)^2 := by
  have hb := radial_budget_hasSum sixPhysical _ 1 six_physical_tendsto K
    (fun j => by simpa only [one_mul] using six_effective_increment_budget (K+j) (by omega))
  simpa only [one_mul] using hb

/-- Recertification of the already known third odd residual by the new
finite-scale source/tail route, with no earlier pivot sign as premise. -/
theorem third_odd_residual_pos_via_effective_budget : 0<
    canonicalCompletedNativeLogDerivativeMoment 5+sixU*canonicalCompletedNativeLogDerivativeMoment 4+
      sixV*canonicalCompletedNativeLogDerivativeMoment 3 := by
  have hp := six_boundary_positive_from_effective_budget
  rw [six_critical_limit_residual] at hp
  linarith

end
end CarryEffectiveRadial
