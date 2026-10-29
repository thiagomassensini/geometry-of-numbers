import NormalizedRemainder
import SixEnergyTransport
import Mathlib.Tactic.Bound

namespace CarryEffectiveRadial
open CarrySelfAdjointOperator CarryMaterialVariation
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
attribute [local irreducible] sourceRemainder canonicalCompletedNativeLogDerivativeMoment

def sixHigherPolynomial (u v : ℝ) (z : ℂ) : ℂ :=
  42*(canonicalCompletedNativeLogDerivativeMoment 3:ℂ)*(v:ℂ)^2+
  3948*(canonicalCompletedNativeLogDerivativeMoment 4:ℂ)*(u:ℂ)*(v:ℂ)+
  1254*(canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(u:ℂ)^2+
  65868*(canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(v:ℂ)+
  32032*(canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(u:ℂ)+
  z^2*(-170*(canonicalCompletedNativeLogDerivativeMoment 4:ℂ)*(v:ℂ)^2-
    75856*(canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(u:ℂ)*(v:ℂ)-
    22880*(canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(u:ℂ)^2-
    3649360*(canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(v:ℂ))+
  z^4*(682*(canonicalCompletedNativeLogDerivativeMoment 5:ℂ)*(v:ℂ)^2+
    1333332*(canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(u:ℂ)*(v:ℂ))+
  z^6*(-2730*(canonicalCompletedNativeLogDerivativeMoment 6:ℂ)*(v:ℂ)^2)

/-- Complete higher readout, after all 36 source crossings were combined.
No higher source coefficient is deleted. -/
def sixEffectiveRemainder (u v : ℝ) (z : ℂ) : ℂ := sixHigherPolynomial u v z-
  (∑ j : Fin 6, sixNodeWeight u v z j*((j:ℂ)+1)^15*
    sourceRemainder 7 (Complex.I*((j:ℂ)+1)*z))/14400

theorem radial_node_norm (z : ℂ) (j : Fin 6) :
    ‖Complex.I*((j:ℂ)+1)*z‖ ≤ 6*‖z‖ := by
  rw [norm_mul,norm_mul,Complex.norm_I,one_mul]
  have hj : ‖(j:ℂ)+1‖ ≤ 6 := by
    have he : ((j:ℂ)+1)=(((j:ℝ)+1:ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hn : (j:ℝ)<6 := by exact_mod_cast j.isLt
    have hN : (j:ℝ)≤5 := by exact_mod_cast (show (j:ℕ)≤5 by omega)
    linarith
  exact mul_le_mul_of_nonneg_right hj (norm_nonneg z)

theorem six_effective_remainder_analytic (u v : ℝ) (z : ℂ) (hz : ‖z‖ < 1/12) :
    AnalyticAt ℂ (sixEffectiveRemainder u v) z := by
  have hp : AnalyticAt ℂ (sixHigherPolynomial u v) z := by unfold sixHigherPolynomial; fun_prop
  have hw (j : Fin 6) : AnalyticAt ℂ (fun z => sixNodeWeight u v z j) z := by
    fin_cases j <;> dsimp [sixNodeWeight] <;> fun_prop
  have hg (j : Fin 6) : AnalyticAt ℂ
      (fun w => sourceRemainder 7 (Complex.I*((j:ℂ)+1)*w)) z := by
    apply (source_remainder_analytic 7 _ (lt_of_le_of_lt (radial_node_norm z j) (by linarith))).fun_comp_of_eq
      (by fun_prop) rfl
  have hs : AnalyticAt ℂ (fun z => ∑ j : Fin 6, sixNodeWeight u v z j*((j:ℂ)+1)^15*
      sourceRemainder 7 (Complex.I*((j:ℂ)+1)*z)) z := by
    have ht (j : Fin 6) : AnalyticAt ℂ
        (fun w => sixNodeWeight u v w j*((j:ℂ)+1)^15*
          sourceRemainder 7 (Complex.I*((j:ℂ)+1)*w)) z :=
      ((hw j).fun_mul (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => ((j:ℂ)+1)^15) z)).fun_mul (hg j)
    convert (Finset.analyticAt_sum (f := fun j w => sixNodeWeight u v w j*((j:ℂ)+1)^15*
      sourceRemainder 7 (Complex.I*((j:ℂ)+1)*w)) Finset.univ (fun j _ => ht j)) using 1
    all_goals rfl
  exact hp.fun_sub (hs.fun_div analyticAt_const (by norm_num))

theorem canonical_moment_norm_le_one (n : ℕ) :
    ‖(canonicalCompletedNativeLogDerivativeMoment n:ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact (source_coefficient_bound n).trans (pow_le_one₀ (by norm_num) (by norm_num))

theorem six_expansion_on_disc (u v : ℝ) (z : ℂ) (hz : ‖z‖ < 1/24) (hn : z≠0)
    (hF : ∀ j : Fin 6, completedNativeOperatorCharacteristic (Complex.I*((j:ℂ)+1)*z)≠0) :
    sixEnergy u v z=(sixLimit u v:ℂ)+(sixCorrection u v:ℂ)*z^2+
      z^4*sixEffectiveRemainder u v z := by
  have ht (j : Fin 6) := native_response_exact_remainder 7 (Complex.I*((j:ℂ)+1)*z)
    (lt_of_le_of_lt (radial_node_norm z j) (by linarith)) (hF j)
  unfold sixEnergy
  rw [six_kernel_reduction]
  simp_rw [ht]
  dsimp [sixEffectiveRemainder,sixHigherPolynomial,sixLimit,sixCorrection]
  generalize hA : canonicalCompletedNativeLogDerivativeMoment = a
  generalize hR : sourceRemainder 7 = R
  norm_num [Fin.sum_univ_succ,sixNodeWeight,Finset.sum_range_succ]
  field_simp [hn]
  ring_nf
  norm_num [Complex.I_pow_eq_pow_mod,Complex.I_sq]
  ring_nf
  norm_num [Complex.I_sq]
  ring

end
end CarryEffectiveRadial
