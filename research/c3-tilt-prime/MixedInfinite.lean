import MixedPrime
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Derivação sob o limite para o canal do tilt (Seção 1)

Este módulo fecha a troca de ordem **altura ↔ soma** do canal isolado do tilt.
Define a resposta transversal infinita `G(t) = ∑' k, mixedTiltWave k t` e prova que
seus jets de altura são obtidos termo a termo:

  `(-1)^n ∂_t^{2n} G(0) = ∑' k, w_k (log c_k)^{2n} > 0`,  para todo `n`.

A soma converge normalmente (`0 ≤ w_k ≤ 2 c_k^{-5/2}`), logo a derivação sob a soma é
legítima em toda ordem. Isto identifica o limite dos jets de prefixo finito
(`finite_mixed_tilt_tendsto_positive`) com o jet do objeto infinito já sintetizado.

NÃO modifica nenhum arquivo do trabalho anterior; apenas acrescenta este canal.
A troca transversal `∂_δ ↔ ∑' k` (via a integral `T_δ`) permanece fora deste módulo.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000

/-- Amplitude material de cada célula: `w_k = c_k^{-1/2} · sensibilidade transversal`. -/
def wCoeff (k : ℕ) : ℝ :=
  canonicalRealCpCenter k ^ (-(1/2:ℝ)) * carryTiltThreeFirstSensitivity (canonicalRealCpCenter k)

theorem wCoeff_nonneg (k : ℕ) : 0 ≤ wCoeff k := by
  unfold wCoeff
  have hc : 0 < canonicalRealCpCenter k := lt_trans zero_lt_one (center_gt_one k)
  exact mul_nonneg (Real.rpow_nonneg hc.le _)
    (carryTiltThreeFirstSensitivity_pos (center_gt_one k)).le

/-- Cota uniforme da derivada de altura de ordem `m` do canal do tilt da célula `k`. -/
def tiltOrderBound (m k : ℕ) : ℝ :=
  wCoeff k * (Real.log (canonicalRealCpCenter k))^m

theorem tiltOrderBound_nonneg (m k : ℕ) : 0 ≤ tiltOrderBound m k :=
  mul_nonneg (wCoeff_nonneg k) (pow_nonneg (Real.log_nonneg (center_gt_one k).le) _)

theorem eventually_log_pow_le_root (m : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      (Real.log (canonicalRealCpCenter k))^m ≤ (canonicalRealCpCenter k)^(1/2:ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop ((m:ℕ):ℝ) (by norm_num : (0:ℝ)<1/2)).bound
    (by norm_num : (0:ℝ)<1)
  have hp := center_tendsto_atTop.eventually h
  filter_upwards [hp] with k hk
  have hc : 0 ≤ canonicalRealCpCenter k := le_of_lt (lt_trans zero_lt_one (center_gt_one k))
  have hl : 0 ≤ Real.log (canonicalRealCpCenter k) := Real.log_nonneg (le_of_lt (center_gt_one k))
  simpa only [one_mul,Real.rpow_natCast,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hl _),abs_of_nonneg (Real.rpow_nonneg hc _)] using hk

theorem eventually_tiltOrderBound_le (m : ℕ) :
    ∀ᶠ k : ℕ in atTop, ‖tiltOrderBound m k‖ ≤ 2 * (((k+1:ℕ):ℝ)^(-2:ℝ)) := by
  filter_upwards [eventually_log_pow_le_root m] with k hlog
  let c : ℝ := canonicalRealCpCenter k
  let j : ℝ := ((k+1:ℕ):ℝ)
  have hj : 0 < j := by dsimp [j]; positivity
  have hj1 : 1 ≤ j := by dsimp [j]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have heq : c = 3*j := by simp [c,j,canonicalRealCpCenter]
  have hc2 : 2 ≤ c := by rw [heq]; nlinarith
  have hc : 0 < c := lt_of_lt_of_le (by norm_num) hc2
  have hw : 0 ≤ c^(-(1/2:ℝ)) := Real.rpow_nonneg hc.le _
  have hroot : 0 < c^(1/2:ℝ) := Real.rpow_pos_of_pos hc _
  have hs : 0 ≤ carryTiltThreeFirstSensitivity c := (carryTiltThreeFirstSensitivity_pos (by linarith)).le
  have hsbound := carryTiltThreeFirstSensitivity_le_two_div_sq hc2
  have hwlog : c^(-(1/2:ℝ)) * (Real.log c)^m ≤ 1 := by
    calc
      _ ≤ c^(-(1/2:ℝ)) * c^(1/2:ℝ) := mul_le_mul_of_nonneg_left hlog hw
      _ = 1 := by rw [Real.rpow_neg hc.le]; exact inv_mul_cancel₀ hroot.ne'
  have hccomp : 2 / c^2 ≤ 2 / j^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hc) (sq_pos_of_pos hj)).2
    rw [heq]; nlinarith [sq_nonneg j]
  have htarget : tiltOrderBound m k ≤ 2 * j^(-2:ℝ) := by
    unfold tiltOrderBound wCoeff
    change (c^(-(1/2:ℝ))*carryTiltThreeFirstSensitivity c)*(Real.log c)^m ≤ _
    calc
      _ = (c^(-(1/2:ℝ))*(Real.log c)^m)*carryTiltThreeFirstSensitivity c := by ring
      _ ≤ 1*carryTiltThreeFirstSensitivity c := mul_le_mul_of_nonneg_right hwlog hs
      _ ≤ 2/c^2 := by simpa using hsbound
      _ ≤ 2/j^2 := hccomp
      _ = 2*j^(-2:ℝ) := by rw [Real.rpow_neg hj.le,Real.rpow_two]; ring
  rw [Real.norm_eq_abs,abs_of_nonneg (tiltOrderBound_nonneg m k)]
  exact htarget

theorem tiltOrderBound_summable (m : ℕ) : Summable (tiltOrderBound m) := by
  have hbase : Summable (fun k : ℕ => (k:ℝ)^(-2:ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := hbase.comp_injective (show Function.Injective (fun k : ℕ => k+1) by
    intro a b hab; exact Nat.add_right_cancel hab)
  have hmajorant : Summable (fun k : ℕ => 2 * (((k+1:ℕ):ℝ)^(-2:ℝ))) := by
    simpa [Function.comp_def] using hshift.mul_left 2
  exact hmajorant.of_norm_bounded_eventually_nat (eventually_tiltOrderBound_le m)

#print axioms tiltOrderBound_summable

/-- Norma da frequência do tilt: `‖-i log c_k‖ = log c_k`. -/
theorem norm_tiltFrequency (k : ℕ) : ‖tiltFrequency k‖ = Real.log (canonicalRealCpCenter k) := by
  have hl : 0 ≤ Real.log (canonicalRealCpCenter k) := Real.log_nonneg (center_gt_one k).le
  simp only [tiltFrequency, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hl]

/-- A fase material é unitária sobre o eixo real. -/
theorem tilt_exp_arg_re_zero (k : ℕ) (t : ℝ) :
    ((-Complex.I*(Real.log (canonicalRealCpCenter k):ℂ))*(t:ℂ)).re = 0 := by
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_mixedTiltWave_ofReal (k : ℕ) (t : ℝ) :
    ‖mixedTiltWave k (t:ℂ)‖ = wCoeff k := by
  have hexp : ‖Complex.exp ((-Complex.I*(Real.log (canonicalRealCpCenter k):ℂ))*(t:ℂ))‖ = 1 := by
    rw [Complex.norm_exp, tilt_exp_arg_re_zero, Real.exp_zero]
  unfold mixedTiltWave
  rw [norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (wCoeff_nonneg k)

/-- Cota uniforme (em `x`) da derivada de Fréchet iterada de ordem `m`. -/
theorem tilt_iteratedFDeriv_bound (m i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ m (fun t : ℝ => mixedTiltWave i (t:ℂ)) x‖ ≤ tiltOrderBound m i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, mixedTiltWave_real_iterated,
    norm_mul, norm_pow, norm_tiltFrequency, norm_mixedTiltWave_ofReal]
  unfold tiltOrderBound
  exact le_of_eq (mul_comm _ _)

theorem tilt_iteratedDeriv_bound (m i : ℕ) (x : ℝ) :
    ‖iteratedDeriv m (fun t : ℝ => mixedTiltWave i (t:ℂ)) x‖ ≤ tiltOrderBound m i := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact tilt_iteratedFDeriv_bound m i x

theorem mixedTiltWave_real_contDiff (i : ℕ) :
    ContDiff ℝ ⊤ (fun t : ℝ => mixedTiltWave i (t:ℂ)) := by
  have hcast : ContDiff ℝ ⊤ (fun u : ℝ => (u:ℂ)) := Complex.ofRealCLM.contDiff
  have he : ContDiff ℝ ⊤ (fun u : ℝ => Complex.exp (tiltFrequency i*(u:ℂ))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul hcast)
  unfold mixedTiltWave
  simpa only [tiltFrequency] using (contDiff_const.mul he)

/-- **Troca altura ↔ soma.** As derivadas de altura de ordem `m` passam pela soma infinita. -/
theorem iteratedDeriv_tsum_mixed (m : ℕ) (x : ℝ) :
    iteratedDeriv m (fun t : ℝ => ∑' k : ℕ, mixedTiltWave k (t:ℂ)) x
      = ∑' k : ℕ, iteratedDeriv m (fun t : ℝ => mixedTiltWave k (t:ℂ)) x := by
  have hF : iteratedFDeriv ℝ m (fun t : ℝ => ∑' k : ℕ, mixedTiltWave k (t:ℂ)) x
      = ∑' k : ℕ, iteratedFDeriv ℝ m (fun t : ℝ => mixedTiltWave k (t:ℂ)) x :=
    iteratedFDeriv_tsum_apply (𝕜:=ℝ) (N:=(m:ℕ∞))
      (fun i => (mixedTiltWave_real_contDiff i).of_le le_top)
      (fun j _ => tiltOrderBound_summable j)
      (fun j i y _ => tilt_iteratedFDeriv_bound j i y)
      le_rfl x
  have hsum : Summable (fun k => iteratedFDeriv ℝ m (fun t : ℝ => mixedTiltWave k (t:ℂ)) x) :=
    Summable.of_norm_bounded (tiltOrderBound_summable m) (fun k => tilt_iteratedFDeriv_bound m k x)
  calc
    iteratedDeriv m (fun t : ℝ => ∑' k : ℕ, mixedTiltWave k (t:ℂ)) x
        = (iteratedFDeriv ℝ m (fun t : ℝ => ∑' k : ℕ, mixedTiltWave k (t:ℂ)) x) (fun _ => 1) :=
          iteratedDeriv_eq_iteratedFDeriv
    _ = (∑' k : ℕ, iteratedFDeriv ℝ m (fun t : ℝ => mixedTiltWave k (t:ℂ)) x) (fun _ => 1) := by
          rw [hF]
    _ = ∑' k : ℕ, (iteratedFDeriv ℝ m (fun t : ℝ => mixedTiltWave k (t:ℂ)) x) (fun _ => 1) := by
          simpa only [ContinuousMultilinearMap.apply_apply] using
            (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℝ) ℂ (fun _ => 1)).map_tsum hsum
    _ = ∑' k : ℕ, iteratedDeriv m (fun t : ℝ => mixedTiltWave k (t:ℂ)) x :=
          tsum_congr (fun _ => (iteratedDeriv_eq_iteratedFDeriv).symm)

#print axioms iteratedDeriv_tsum_mixed

/-- Resposta transversal infinita `G(t) = ∂_δ W_∞(0,t) = ∑' k, w_k e^{-it log c_k}`. -/
def infiniteMixedTiltResponse (z : ℂ) : ℂ := ∑' k : ℕ, mixedTiltWave k z

/-- **Identidade da derivação sob o limite** (caixa da Seção 1). -/
theorem infinite_mixed_tilt_identity (n : ℕ) :
    ((-1:ℂ)^n * iteratedDeriv (2*n)
        (fun t : ℝ => infiniteMixedTiltResponse (t:ℂ)) 0).re
      = ∑' k : ℕ, mixedTiltTerm n k := by
  have hsum0 : Summable (fun k => iteratedDeriv (2*n) (fun t : ℝ => mixedTiltWave k (t:ℂ)) 0) :=
    Summable.of_norm_bounded (tiltOrderBound_summable (2*n))
      (fun k => tilt_iteratedDeriv_bound (2*n) k 0)
  have hsum : Summable
      (fun k => (-1:ℂ)^n * iteratedDeriv (2*n) (fun t : ℝ => mixedTiltWave k (t:ℂ)) 0) :=
    hsum0.mul_left _
  unfold infiniteMixedTiltResponse
  rw [iteratedDeriv_tsum_mixed (2*n) 0, ← tsum_mul_left, Complex.re_tsum hsum]
  apply tsum_congr
  intro k
  have hfun : (fun u : ℝ =>
        deriv (fun d : ℝ => canonicalCriticalWeightedTiltBlock k (displacedParameter d u)) 0)
      = (fun u : ℝ => mixedTiltWave k (u:ℂ)) := by
    funext u; exact mixed_tilt_wave_of_real k u
  have h := signed_even_mixed_tilt k n
  rw [hfun] at h
  exact h

#print axioms infinite_mixed_tilt_identity

/-- Os jets mistos do tilt infinito são estritamente positivos em toda ordem par. -/
theorem infinite_mixed_tilt_positive (n : ℕ) :
    0 < ((-1:ℂ)^n * iteratedDeriv (2*n)
        (fun t : ℝ => infiniteMixedTiltResponse (t:ℂ)) 0).re := by
  rw [infinite_mixed_tilt_identity]
  exact mixedTiltTerm_tsum_pos n

#print axioms infinite_mixed_tilt_positive

/-- Mesma identidade reescrita pelas profundidades das câmeras primas (ponte da PR #47). -/
theorem infinite_mixed_prime_depth_identity (n : ℕ) :
    ((-1:ℂ)^n * iteratedDeriv (2*n)
        (fun t : ℝ => infiniteMixedTiltResponse (t:ℂ)) 0).re
      = ∑' k : ℕ, primeDepthMixedTiltTerm n k := by
  rw [infinite_mixed_tilt_identity]
  exact tsum_congr (fun k => mixedTiltTerm_eq_primeDepth n k)

#print axioms infinite_mixed_prime_depth_identity

/-- **Capstone:** os jets de prefixo finito convergem para o jet do objeto infinito. -/
theorem finite_jets_tendsto_infinite_jet (n : ℕ) :
    Tendsto (fun M : ℕ => ((-1:ℂ)^n * iteratedDeriv (2*n) (fun t : ℝ =>
        deriv (fun d : ℝ =>
          finiteCanonicalCriticalWeightedTiltTrace M (displacedParameter d t)) 0) 0).re)
      atTop
      (nhds (((-1:ℂ)^n * iteratedDeriv (2*n)
        (fun t : ℝ => infiniteMixedTiltResponse (t:ℂ)) 0).re)) := by
  rw [infinite_mixed_tilt_identity]
  exact finite_mixed_tilt_tendsto_positive n

#print axioms finite_jets_tendsto_infinite_jet

end
end CarryTiltSlice
