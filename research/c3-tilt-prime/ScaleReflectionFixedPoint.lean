import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `1/2` como ponto fixo da involução de escala (invariante provado, só sinal)

A lei de escala tem uma reflexão `δ ↦ -δ` (com `δ = σ - 1/2`, isto é `σ ↦ 1 - σ`). O
conteúdo intrínseco é: **`1/2` é o único ponto fixo dessa involução onde a leitura é
auto-dual**, e isso é um fato de *sinal*, não de localização de zeros.

Na métrica centrada, o tilt normalizado numa célula de centro `c` é
`U_δ(c) = (1-1/c)^{-δ} + (1+1/c)^{-δ} - 2`. Sua reflexão simétrica

`reflectedNormalizedTilt c δ = U_δ(c) + U_{-δ}(c)
  = (1-1/c)^{-δ}+(1-1/c)^{δ} + (1+1/c)^{-δ}+(1+1/c)^{δ} - 4`

é **invariante por `δ ↦ -δ`** (`reflectedNormalizedTilt_reflection`), é **sempre ≥ 0**
(`reflectedNormalizedTilt_nonneg`) e **zera exatamente em `δ = 0`**
(`reflectedNormalizedTilt_eq_zero_iff`), estritamente positiva fora
(`reflectedNormalizedTilt_pos_of_ne_zero`). Logo `δ = 0` (`σ = 1/2`) é o único ponto
auto-dual: a compatibilidade entre escalas só vale lá, e a "distância à auto-dualidade" é
uma quantidade positiva genuína em todo o resto.

Mecanismo: para `a > 0`, `a^δ + a^{-δ} = (a^δ) + (a^δ)⁻¹ ≥ 2`, com igualdade sse `δ = 0`
quando `a ≠ 1`. Nas pernas `a = 1 ∓ 1/c` (ambas `≠ 1` para `c > 1`), isso força o ponto
fixo. Matriz e sinal; nada de zeros, nada de RH. Auto-contido (só Mathlib).
-/

namespace CarryTiltSlice
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Desigualdade escalar de auto-dualidade -/

/-- Para `a > 0`, `a^δ + a^{-δ} ≥ 2` (média aritmética–geométrica na reflexão). -/
theorem two_le_rpow_add_rpow_neg {a : ℝ} (ha : 0 < a) (δ : ℝ) :
    2 ≤ a ^ δ + a ^ (-δ) := by
  have hx : 0 < a ^ δ := Real.rpow_pos_of_pos ha δ
  have hinv : a ^ (-δ) = (a ^ δ)⁻¹ := Real.rpow_neg ha.le δ
  rw [hinv]
  have hcancel : a ^ δ * (a ^ δ)⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
  nlinarith [sq_nonneg (a ^ δ - 1), hx, hcancel]

/-- Com `a > 0` e `a ≠ 1`, a igualdade `a^δ + a^{-δ} = 2` vale **apenas** no ponto fixo
`δ = 0`. -/
theorem rpow_add_rpow_neg_eq_two_iff {a : ℝ} (ha : 0 < a) (hane : a ≠ 1) (δ : ℝ) :
    a ^ δ + a ^ (-δ) = 2 ↔ δ = 0 := by
  have hx : 0 < a ^ δ := Real.rpow_pos_of_pos ha δ
  have hinv : a ^ (-δ) = (a ^ δ)⁻¹ := Real.rpow_neg ha.le δ
  constructor
  · intro h
    rw [hinv] at h
    have hxinv : (a ^ δ)⁻¹ = 2 - a ^ δ := by linarith
    have hcancel : a ^ δ * (a ^ δ)⁻¹ = 1 := mul_inv_cancel₀ hx.ne'
    rw [hxinv] at hcancel
    have hsq : (a ^ δ - 1) ^ 2 = 0 := by linear_combination -hcancel
    have hx1 : a ^ δ = 1 := by
      have := (pow_eq_zero_iff (two_ne_zero)).mp hsq
      linarith
    have hlog : δ * Real.log a = 0 := by
      have hh := congrArg Real.log hx1
      rwa [Real.log_rpow ha, Real.log_one] at hh
    have hla : Real.log a ≠ 0 := by
      intro h0
      rcases Real.log_eq_zero.mp h0 with h' | h' | h'
      · exact ha.ne' h'
      · exact hane h'
      · linarith
    exact (mul_eq_zero.mp hlog).resolve_right hla
  · intro h
    subst h
    norm_num [Real.rpow_zero]

/-! ## Reflexão normalizada do tilt e o ponto fixo `1/2` -/

/-- Reflexão simétrica do tilt normalizado ao centro: `U_δ(c) + U_{-δ}(c)`. -/
def reflectedNormalizedTilt (c δ : ℝ) : ℝ :=
  (1 - 1 / c) ^ (-δ) + (1 - 1 / c) ^ δ + ((1 + 1 / c) ^ (-δ) + (1 + 1 / c) ^ δ) - 4

/-- **Invariância pela involução de escala `δ ↦ -δ`.** -/
theorem reflectedNormalizedTilt_reflection (c δ : ℝ) :
    reflectedNormalizedTilt c (-δ) = reflectedNormalizedTilt c δ := by
  unfold reflectedNormalizedTilt; rw [neg_neg]; ring

/-- A reflexão normalizada é **não negativa** para todo centro `c > 1`. -/
theorem reflectedNormalizedTilt_nonneg {c : ℝ} (hc : 1 < c) (δ : ℝ) :
    0 ≤ reflectedNormalizedTilt c δ := by
  have hc0 : 0 < c := by linarith
  have hinvc : 0 < 1 / c := div_pos one_pos hc0
  have hone : 1 / c < 1 := by rw [div_lt_one hc0]; linarith
  have ha1 : 0 < 1 - 1 / c := by linarith
  have ha2 : 0 < 1 + 1 / c := by linarith
  have h1 := two_le_rpow_add_rpow_neg ha1 δ
  have h2 := two_le_rpow_add_rpow_neg ha2 δ
  unfold reflectedNormalizedTilt
  nlinarith [h1, h2]

/-- **`δ = 0` é o único ponto auto-dual.** A reflexão normalizada zera exatamente no ponto
fixo `δ = 0` (isto é `σ = 1/2`). -/
theorem reflectedNormalizedTilt_eq_zero_iff {c : ℝ} (hc : 1 < c) (δ : ℝ) :
    reflectedNormalizedTilt c δ = 0 ↔ δ = 0 := by
  have hc0 : 0 < c := by linarith
  have hinvc : 0 < 1 / c := div_pos one_pos hc0
  have hone : 1 / c < 1 := by rw [div_lt_one hc0]; linarith
  have ha1 : 0 < 1 - 1 / c := by linarith
  have ha2 : 0 < 1 + 1 / c := by linarith
  have ha1ne : 1 - 1 / c ≠ 1 := ne_of_lt (by linarith)
  constructor
  · intro h
    have h1 := two_le_rpow_add_rpow_neg ha1 δ
    have h2 := two_le_rpow_add_rpow_neg ha2 δ
    have e1 : (1 - 1 / c) ^ δ + (1 - 1 / c) ^ (-δ) = 2 := by
      unfold reflectedNormalizedTilt at h; linarith
    exact (rpow_add_rpow_neg_eq_two_iff ha1 ha1ne δ).mp e1
  · intro h
    subst h
    simp only [reflectedNormalizedTilt, neg_zero, Real.rpow_zero]
    norm_num

/-- Fora do ponto fixo a reflexão normalizada é **estritamente positiva**: a distância à
auto-dualidade é positiva em toda escala `δ ≠ 0`. -/
theorem reflectedNormalizedTilt_pos_of_ne_zero {c : ℝ} (hc : 1 < c) {δ : ℝ} (hδ : δ ≠ 0) :
    0 < reflectedNormalizedTilt c δ :=
  lt_of_le_of_ne (reflectedNormalizedTilt_nonneg hc δ)
    (fun h => hδ ((reflectedNormalizedTilt_eq_zero_iff hc δ).mp h.symm))

#print axioms two_le_rpow_add_rpow_neg
#print axioms rpow_add_rpow_neg_eq_two_iff
#print axioms reflectedNormalizedTilt_reflection
#print axioms reflectedNormalizedTilt_eq_zero_iff
#print axioms reflectedNormalizedTilt_pos_of_ne_zero

end
end CarryTiltSlice
