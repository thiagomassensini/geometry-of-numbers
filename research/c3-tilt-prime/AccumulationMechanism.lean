import LpNormBridge
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Mecanismo de acúmulo na ordem

Formaliza duas peças concretas da hipótese "o defeito transversal cresce na ordem mais
rápido do que a parte positiva absorve":

1. **Crescimento dos jets do tilt.** Com `M_m = Σ_k w_k (log c_k)^{2m} = ‖L^m v‖²` e `c_k ≥ 3`,
   `M_{m+1} ≥ (log 3)² M_m`, logo `M_m ≥ (log 3)^{2m} M_0 → +∞`. As potências do relógio
   logarítmico amplificam esse canal com a ordem.

2. **Modelo harmônico de acúmulo.** No modelo de formas quadráticas `H_N(δ) = I_N − δ² v_N v_N^*`
   com `v_N = (1,1/√2,…,1/√N)`, a forma avaliada em `v_N` é `‖v_N‖²(1 − δ²‖v_N‖²)`, com
   `‖v_N‖² = Σ_{k<N} 1/(k+1)`. Como a série harmônica diverge, para **todo** `δ ≠ 0` existe `N`
   finito com uma direção negativa — o deslocamento, por menor que seja, acaba detectado.

Honestidade: (1) é o crescimento dos jets **positivos** do canal do tilt, não prova que a parte
negativa vença a fonte completa. (2) é um modelo de formas quadráticas, não a fonte C3. O programa
restante (razão `R_N(δ) = sup D_δ/P_δ`) exige a decomposição `Q_δ = P_δ − D_δ` da fonte física.

Não modifica nenhum módulo anterior.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## 1. Crescimento dos jets pares do tilt -/

/-- Jet par de ordem `m` do canal do tilt: `M_m = Σ_k w_k (log c_k)^{2m} = ‖L^m v‖²`. -/
def tiltJet (m : ℕ) : ℝ := ∑' k : ℕ, mixedTiltTerm m k

theorem tiltJet_eq_lp_normSq (m : ℕ) : tiltJet m = ‖tiltLpVector m‖ ^ 2 :=
  (tiltLpVector_normSq m).symm

theorem canonicalRealCpCenter_ge_three (k : ℕ) : (3 : ℝ) ≤ canonicalRealCpCenter k := by
  unfold canonicalRealCpCenter
  have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  nlinarith

theorem mixedTiltTerm_succ (m k : ℕ) :
    mixedTiltTerm (m + 1) k = mixedTiltTerm m k * (Real.log (canonicalRealCpCenter k)) ^ 2 := by
  unfold mixedTiltTerm
  rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
  ring

/-- Cada passo de ordem amplifica o jet por ao menos `(log 3)²`. -/
theorem tiltJet_growth (m : ℕ) : (Real.log 3) ^ 2 * tiltJet m ≤ tiltJet (m + 1) := by
  unfold tiltJet
  rw [← tsum_mul_left]
  refine ((mixedTiltTerm_summable m).mul_left ((Real.log 3) ^ 2)).tsum_le_tsum
    (fun k => ?_) (mixedTiltTerm_summable (m + 1))
  rw [mixedTiltTerm_succ]
  have hc : (3 : ℝ) ≤ canonicalRealCpCenter k := canonicalRealCpCenter_ge_three k
  have h3nn : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 3 ≤ Real.log (canonicalRealCpCenter k) :=
    Real.log_le_log (by norm_num) hc
  have hsq : (Real.log 3) ^ 2 ≤ (Real.log (canonicalRealCpCenter k)) ^ 2 :=
    pow_le_pow_left₀ h3nn hlog 2
  have hpos : 0 ≤ mixedTiltTerm m k := (mixedTiltTerm_pos m k).le
  calc (Real.log 3) ^ 2 * mixedTiltTerm m k
      ≤ (Real.log (canonicalRealCpCenter k)) ^ 2 * mixedTiltTerm m k :=
        mul_le_mul_of_nonneg_right hsq hpos
    _ = mixedTiltTerm m k * (Real.log (canonicalRealCpCenter k)) ^ 2 := mul_comm _ _

theorem logThreeSq_gt_one : 1 < (Real.log 3) ^ 2 := by
  have he : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have hlog : 1 < Real.log 3 := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_lt_log (Real.exp_pos 1) he
  nlinarith

/-- Cota geométrica: `M_m ≥ (log 3)^{2m} M_0`. -/
theorem tiltJet_ge_geom (m : ℕ) : (Real.log 3) ^ (2 * m) * tiltJet 0 ≤ tiltJet m := by
  induction m with
  | zero => simp
  | succ n ih =>
    calc (Real.log 3) ^ (2 * (n + 1)) * tiltJet 0
        = (Real.log 3) ^ 2 * ((Real.log 3) ^ (2 * n) * tiltJet 0) := by
          rw [show 2 * (n + 1) = 2 + 2 * n by ring, pow_add]; ring
      _ ≤ (Real.log 3) ^ 2 * tiltJet n :=
          mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ tiltJet (n + 1) := tiltJet_growth n

/-- **Os jets pares do tilt divergem com a ordem** (o relógio logarítmico amplifica o canal). -/
theorem tiltJet_tendsto_atTop : Tendsto tiltJet atTop atTop := by
  have h0 : 0 < tiltJet 0 := mixedTiltTerm_tsum_pos 0
  have hpow : Tendsto (fun m => (Real.log 3) ^ (2 * m)) atTop atTop := by
    refine (tendsto_pow_atTop_atTop_of_one_lt logThreeSq_gt_one).congr (fun m => ?_)
    rw [pow_mul]
  exact tendsto_atTop_mono tiltJet_ge_geom (hpow.atTop_mul_const h0)

/-- Mesma divergência na forma de norma ℓ²: `‖L^m v‖² → +∞`. -/
theorem lp_normSq_tendsto_atTop : Tendsto (fun m => ‖tiltLpVector m‖ ^ 2) atTop atTop := by
  refine tiltJet_tendsto_atTop.congr (fun m => ?_)
  exact tiltJet_eq_lp_normSq m

#print axioms tiltJet_growth
#print axioms tiltJet_tendsto_atTop
#print axioms lp_normSq_tendsto_atTop

/-! ## 2. Modelo harmônico de acúmulo (formas quadráticas) -/

/-- `‖v_N‖² = Σ_{k<N} 1/(k+1)`, a soma harmônica parcial. -/
def harmonicSum (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, (1 / (k + 1) : ℝ)

theorem harmonicSum_tendsto_atTop : Tendsto harmonicSum atTop atTop :=
  Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- No modelo `H_N(δ) = I_N − δ² v_N v_N^*`, a forma em `v_N` é `‖v_N‖²(1 − δ²‖v_N‖²)`:
para **todo** `δ ≠ 0` existe ordem `N` com direção estritamente negativa. -/
theorem toy_negative_direction {δ : ℝ} (hδ : δ ≠ 0) :
    ∃ N : ℕ, harmonicSum N * (1 - δ ^ 2 * harmonicSum N) < 0 := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  obtain ⟨N, hN⟩ := (harmonicSum_tendsto_atTop.eventually_gt_atTop (1 / δ ^ 2)).exists
  refine ⟨N, ?_⟩
  have hpos : 0 < harmonicSum N := lt_trans (by positivity) hN
  rw [div_lt_iff₀ hδ2] at hN
  exact mul_neg_of_pos_of_neg hpos (by nlinarith)

#print axioms harmonicSum_tendsto_atTop
#print axioms toy_negative_direction

end
end CarryTiltSlice
