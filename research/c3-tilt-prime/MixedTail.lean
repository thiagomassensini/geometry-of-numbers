import MixedFinite
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

def mixedTiltTerm (n k : ℕ) : ℝ :=
  (canonicalRealCpCenter k ^ (-(1/2:ℝ)) *
    carryTiltThreeFirstSensitivity (canonicalRealCpCenter k)) *
      (Real.log (canonicalRealCpCenter k))^(2*n)

theorem mixedTiltTerm_pos (n k : ℕ) : 0 < mixedTiltTerm n k := by
  unfold mixedTiltTerm
  have h := signed_even_mixed_tilt_pos k n
  rw [signed_even_mixed_tilt] at h
  exact h

theorem center_tendsto_atTop : Tendsto canonicalRealCpCenter atTop atTop := by
  have hn : Tendsto (fun k : ℕ => ((k+1:ℕ):ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun k : ℕ => (3:ℝ)*((k+1:ℕ):ℝ)) atTop atTop
  exact hn.const_mul_atTop (by norm_num : (0:ℝ)<3)

theorem eventually_log_even_le_root (n : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      (Real.log (canonicalRealCpCenter k))^(2*n) ≤
        (canonicalRealCpCenter k)^(1/2:ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop ((2*n:ℕ):ℝ) (by norm_num : (0:ℝ)<1/2)).bound (by norm_num : (0:ℝ)<1)
  have hp := center_tendsto_atTop.eventually h
  filter_upwards [hp] with k hk
  have hc : 0 ≤ canonicalRealCpCenter k := le_of_lt (lt_trans zero_lt_one (center_gt_one k))
  have hl : 0 ≤ Real.log (canonicalRealCpCenter k) := Real.log_nonneg (le_of_lt (center_gt_one k))
  simpa only [one_mul,Real.rpow_natCast,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hl _),abs_of_nonneg (Real.rpow_nonneg hc _)] using hk

theorem eventually_mixed_term_le (n : ℕ) :
    ∀ᶠ k : ℕ in atTop, ‖mixedTiltTerm n k‖ ≤
      2 * (((k+1:ℕ):ℝ)^(-2:ℝ)) := by
  filter_upwards [eventually_log_even_le_root n] with k hlog
  let c := canonicalRealCpCenter k
  let j : ℝ := ((k+1:ℕ):ℝ)
  have hj : 0 < j := by dsimp [j]; positivity
  have hj1 : 1 ≤ j := by dsimp [j]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have heq : c=3*j := by simp [c,j,canonicalRealCpCenter]
  have hc2 : 2 ≤ c := by rw [heq]; nlinarith
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) hc2
  have hw : 0 ≤ c^(-(1/2:ℝ)) := Real.rpow_nonneg hc.le _
  have hroot : 0 < c^(1/2:ℝ) := Real.rpow_pos_of_pos hc _
  have hs : 0 ≤ carryTiltThreeFirstSensitivity c := (carryTiltThreeFirstSensitivity_pos (by linarith)).le
  have hsbound := carryTiltThreeFirstSensitivity_le_two_div_sq hc2
  have hl0 : 0 ≤ (Real.log c)^(2*n) := pow_nonneg (Real.log_nonneg (by linarith)) _
  have hwlog : c^(-(1/2:ℝ)) * (Real.log c)^(2*n) ≤ 1 := by
    calc
      _ ≤ c^(-(1/2:ℝ)) * c^(1/2:ℝ) := mul_le_mul_of_nonneg_left hlog hw
      _ = 1 := by rw [Real.rpow_neg hc.le]; exact inv_mul_cancel₀ hroot.ne'
  have hccomp : 2 / c^2 ≤ 2 / j^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hc) (sq_pos_of_pos hj)).2
    rw [heq]
    nlinarith [sq_nonneg j]
  have htarget : mixedTiltTerm n k ≤ 2 * j^(-2:ℝ) := by
    unfold mixedTiltTerm
    change (c^(-(1/2:ℝ))*carryTiltThreeFirstSensitivity c)*(Real.log c)^(2*n) ≤ _
    calc
      _ = (c^(-(1/2:ℝ))*(Real.log c)^(2*n))*carryTiltThreeFirstSensitivity c := by ring
      _ ≤ 1*carryTiltThreeFirstSensitivity c := mul_le_mul_of_nonneg_right hwlog hs
      _ ≤ 2/c^2 := by simpa using hsbound
      _ ≤ 2/j^2 := hccomp
      _ = 2*j^(-2:ℝ) := by rw [Real.rpow_neg hj.le,Real.rpow_two]; ring
  rw [Real.norm_eq_abs,abs_of_pos (mixedTiltTerm_pos n k)]
  exact htarget

theorem mixedTiltTerm_summable (n : ℕ) : Summable (mixedTiltTerm n) := by
  have hbase : Summable (fun k : ℕ => (k:ℝ)^(-2:ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := hbase.comp_injective (show Function.Injective (fun k : ℕ => k+1) by
    intro a b hab
    exact Nat.add_right_cancel hab)
  have hmajorant : Summable (fun k : ℕ => 2 * (((k+1:ℕ):ℝ)^(-2:ℝ))) := by
    simpa [Function.comp_def] using hshift.mul_left 2
  exact hmajorant.of_norm_bounded_eventually_nat (eventually_mixed_term_le n)

theorem mixedTiltTerm_tsum_pos (n : ℕ) : 0 < ∑' k : ℕ, mixedTiltTerm n k :=
  (mixedTiltTerm_summable n).tsum_pos (fun k => (mixedTiltTerm_pos n k).le) 0 (mixedTiltTerm_pos n 0)

theorem finite_mixed_tilt_tendsto_positive (n : ℕ) :
    Tendsto (fun M : ℕ => ((-1:ℂ)^n * iteratedDeriv (2*n) (fun t : ℝ =>
      deriv (fun d : ℝ => finiteCanonicalCriticalWeightedTiltTrace M (displacedParameter d t)) 0) 0).re)
      atTop (nhds (∑' k : ℕ, mixedTiltTerm n k)) := by
  have h := (mixedTiltTerm_summable n).hasSum.tendsto_sum_nat
  refine h.congr' (Eventually.of_forall fun M => ?_)
  symm
  simpa only [mixedTiltTerm] using finite_mixed_tilt_identity M n

#print axioms mixedTiltTerm_summable
#print axioms mixedTiltTerm_tsum_pos
#print axioms finite_mixed_tilt_tendsto_positive
end
end CarryTiltSlice
