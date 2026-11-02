import MixedTransverse
import OfflineObstruction
import SourceSchurShift

/-!
# Fase B (perna local) — concavidade do pivô na linha autodual

Backbone algébrico da negatividade local, sobre o modelo de deformação já existente
`even_schur_shift : sourceSchur (perturb c 5 d) false 2 = sourceSchur c false 2 − 5·c₀·d`.

O pivô é **linear** no deslocamento `d` do quinto coeficiente, com inclinação `−5c₀ < 0`.
Logo:
* o pivô é estritamente **antitônico** em `d` (a alavanca);
* a configuração da linha (`d=0`) é o **máximo estrito** do pivô se `c₅` tem mínimo
  estrito na linha (`d>0` fora dela);
* um deslocamento `d` que cruza o limiar `pivô₀/(5c₀)` força o pivô `≤ 0` (resp. `< 0`),
  obstruindo a positividade genuína (liga-se à Fase A).

Também registra a **curvatura do tilt** `∂²_δ cpTilt 3 δ c` (a segunda diferença de
`(log x)²`), o mecanismo físico que deve produzir o mínimo estrito de `c₅` na linha.
O sinal físico completo (com peso do carrier e jato de altura) é a obrigação restante.

Não modifica nenhum módulo anterior.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator CarrySourceBezout CarrySourceDimensionThree
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Backbone: o pivô é linear (inclinação −5c₀) no deslocamento de c₅ -/

/-- O pivô par é estritamente decrescente no deslocamento de `c₅`. -/
theorem even_pivot_shift_strict_anti (c : ℕ → ℝ) (hc0 : 0 < c 0) {d₁ d₂ : ℝ} (h : d₁ < d₂) :
    sourceSchur (perturb c 5 d₂) false 2 < sourceSchur (perturb c 5 d₁) false 2 := by
  rw [even_schur_shift, even_schur_shift]; nlinarith

/-- O pivô ímpar é estritamente decrescente no deslocamento de `c₆`. -/
theorem odd_pivot_shift_strict_anti (c : ℕ → ℝ) (hc0 : 0 < c 0) {d₁ d₂ : ℝ} (h : d₁ < d₂) :
    sourceSchur (perturb c 6 d₂) true 2 < sourceSchur (perturb c 6 d₁) true 2 := by
  rw [odd_schur_shift, odd_schur_shift]; nlinarith

/-- A configuração da linha maximiza estritamente o pivô par: qualquer deslocamento
positivo de `c₅` (mínimo estrito na linha) baixa o pivô. -/
theorem even_pivot_strict_max_at_line (c : ℕ → ℝ) (hc0 : 0 < c 0) {d : ℝ} (hd : 0 < d) :
    sourceSchur (perturb c 5 d) false 2 < sourceSchur c false 2 := by
  rw [even_schur_shift]; nlinarith

/-- Versão ímpar. -/
theorem odd_pivot_strict_max_at_line (c : ℕ → ℝ) (hc0 : 0 < c 0) {d : ℝ} (hd : 0 < d) :
    sourceSchur (perturb c 6 d) true 2 < sourceSchur c true 2 := by
  rw [odd_schur_shift]; nlinarith

/-! ## Limiar quantitativo do deslocamento e obstrução -/

/-- Um deslocamento de `c₅` no (ou acima do) limiar `pivô₀/(5c₀)` leva o pivô a `≤ 0`. -/
theorem even_shift_forces_nonpos (c : ℕ → ℝ) {d : ℝ}
    (hd : sourceSchur c false 2 ≤ 5 * c 0 * d) :
    sourceSchur (perturb c 5 d) false 2 ≤ 0 := by
  rw [even_schur_shift]; linarith

/-- Deslocamento estrito acima do limiar: pivô `< 0` (negatividade estrita fora da linha). -/
theorem even_shift_forces_neg (c : ℕ → ℝ) {d : ℝ}
    (hd : sourceSchur c false 2 < 5 * c 0 * d) :
    sourceSchur (perturb c 5 d) false 2 < 0 := by
  rw [even_schur_shift]; linarith

/-- Versão ímpar não estrita. -/
theorem odd_shift_forces_nonpos (c : ℕ → ℝ) {d : ℝ}
    (hd : sourceSchur c true 2 ≤ 6 * c 0 * d) :
    sourceSchur (perturb c 6 d) true 2 ≤ 0 := by
  rw [odd_schur_shift]; linarith

/-- Versão ímpar estrita. -/
theorem odd_shift_forces_neg (c : ℕ → ℝ) {d : ℝ}
    (hd : sourceSchur c true 2 < 6 * c 0 * d) :
    sourceSchur (perturb c 6 d) true 2 < 0 := by
  rw [odd_schur_shift]; linarith

/-- Ligação com a Fase A: um deslocamento estrito acima do limiar obstrui a
positividade genuína da configuração deslocada. -/
theorem even_shift_obstructs_genuine (c : ℕ → ℝ) {d : ℝ}
    (hd : sourceSchur c false 2 < 5 * c 0 * d)
    (hgenuine : 0 < sourceSchur (perturb c 5 d) false 2) : False := by
  have := even_shift_forces_neg c hd; linarith

theorem odd_shift_obstructs_genuine (c : ℕ → ℝ) {d : ℝ}
    (hd : sourceSchur c true 2 < 6 * c 0 * d)
    (hgenuine : 0 < sourceSchur (perturb c 6 d) true 2) : False := by
  have := odd_shift_forces_neg c hd; linarith

#print axioms even_pivot_shift_strict_anti
#print axioms even_shift_forces_neg
#print axioms even_shift_obstructs_genuine

/-! ## Curvatura do tilt na linha (segunda diferença de (log x)²) -/

/-- Segunda derivada em `δ` do tilt C3 — a segunda diferença de `(log x)²·x^{-δ}`. -/
def cpTiltThreeSecondDeriv (c δ : ℝ) : ℝ :=
  (Real.log (c - 1))^2 * (c - 1) ^ (-δ) + (Real.log (c + 1))^2 * (c + 1) ^ (-δ) -
    2 * (Real.log c)^2 * c ^ (-δ)

theorem hasDerivAt_cpTiltThreeDeriv (c : ℝ) (hc : 1 < c) (δ : ℝ) :
    HasDerivAt (fun d : ℝ => cpTiltThreeDeriv c d) (cpTiltThreeSecondDeriv c δ) δ := by
  have hA : HasDerivAt (fun d : ℝ => (-Real.log (c - 1)) * (c - 1) ^ (-d))
      ((Real.log (c - 1))^2 * (c - 1) ^ (-δ)) δ :=
    (((hasDerivAt_neg' δ).const_rpow (show (0:ℝ) < c - 1 by linarith)).const_mul
      (-Real.log (c - 1))).congr_deriv (by ring)
  have hB : HasDerivAt (fun d : ℝ => (-Real.log (c + 1)) * (c + 1) ^ (-d))
      ((Real.log (c + 1))^2 * (c + 1) ^ (-δ)) δ :=
    (((hasDerivAt_neg' δ).const_rpow (show (0:ℝ) < c + 1 by linarith)).const_mul
      (-Real.log (c + 1))).congr_deriv (by ring)
  have hC : HasDerivAt (fun d : ℝ => 2 * Real.log c * c ^ (-d))
      (-(2 * (Real.log c)^2 * c ^ (-δ))) δ :=
    (((hasDerivAt_neg' δ).const_rpow (show (0:ℝ) < c by linarith)).const_mul
      (2 * Real.log c)).congr_deriv (by ring)
  have hcomb := (hA.add hB).add hC
  rw [show (fun d : ℝ => cpTiltThreeDeriv c d) =
      (fun d : ℝ => (-Real.log (c - 1)) * (c - 1) ^ (-d) + (-Real.log (c + 1)) * (c + 1) ^ (-d) +
        2 * Real.log c * c ^ (-d)) by funext d; unfold cpTiltThreeDeriv; ring]
  refine hcomb.congr_deriv ?_
  unfold cpTiltThreeSecondDeriv
  ring

/-- Na linha (`δ=0`) a curvatura do tilt é a segunda diferença de `(log x)²`. -/
theorem cpTiltThreeSecondDeriv_zero (c : ℝ) :
    cpTiltThreeSecondDeriv c 0 =
      (Real.log (c - 1))^2 + (Real.log (c + 1))^2 - 2 * (Real.log c)^2 := by
  unfold cpTiltThreeSecondDeriv
  simp [Real.rpow_zero]

#print axioms hasDerivAt_cpTiltThreeDeriv
#print axioms cpTiltThreeSecondDeriv_zero

end
end CarryTiltSlice
