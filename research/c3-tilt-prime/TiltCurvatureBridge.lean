import CriticalCurvature
import SourceDecomposition

/-!
# Ponte física (nível de célula): curvatura → forma `P·(1 − r)` da obstrução

Liga a curvatura por célula já provada negativa (`cpTiltThreeSecondDeriv c 0 < 0`,
em `CriticalCurvature`) à **mesma estrutura algébrica** `P·(1 − R)` do pivô deformado
(`SourceDecomposition`), só que agora na própria fonte do tilt, célula a célula.

A fonte do tilt numa célula é `cpTilt 3 δ c`. Em `δ = 0` ela se anula
(`cpTilt_three_zero`, em acordo com `weighted_tilt_zero`). Seu 2-jato em `δ` é

\[
  \text{cpTilt}_3(\delta,c) = \underbrace{L(c)}_{>0}\,\delta
    + \tfrac12\,\underbrace{K(c)}_{<0}\,\delta^2 + o(\delta^2),
  \qquad L(c) = \texttt{carryTiltThreeFirstSensitivity}\,c,\;
  K(c) = \texttt{cpTiltThreeSecondDeriv}\,c\,0,
\]

onde `L(c)` é **exatamente** a sensibilidade transversal positiva que já aparece dentro
de `wCoeff`/`mixedTiltTerm`, e `K(c)` é a curvatura negativa da linha. O modelo
quadrático `tiltCellQuadModel` tem o mesmo valor (`0`), a mesma inclinação (`L(c)`) e a
mesma curvatura (`K(c)`) da fonte real em `δ = 0`, e fatora como

\[ \text{tiltCellQuadModel}(c,\delta) = L(c)\,\delta\,(1 - r_c(\delta)),
   \qquad r_c(\delta) = \frac{-K(c)}{2L(c)}\,\delta. \]

Isto é a forma `P·(1 − R)`: para `δ > 0` a célula é positiva enquanto `r_c < 1`, zera no
ponto de virada `δ = 2L/(-K)` e fica **negativa** depois — a curvatura é o déficit que
vira a célula, o análogo microscópico de `even_pivot_neg_iff_ratio_gt_one`.

Honestidade: `tiltCellQuadModel` é o **2-jato** da fonte do tilt por célula (casa valor,
inclinação e curvatura), não o coeficiente completo `c₅` (que ainda inclui carrier,
cruzamentos, bordo, cauda e o jato de altura de ordem 10). A tradução deste ponto de
virada por célula ao deslocamento `d(δ)` da fonte de Schur continua sendo a obrigação
física da Seção D. Nenhum módulo anterior é modificado.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
open Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## A fonte do tilt por célula se anula na linha -/

/-- Na linha autodual (`δ = 0`) a fonte do tilt em cada célula é nula. -/
theorem cpTilt_three_zero (c : ℝ) : cpTilt 3 0 c = 0 := by
  rw [cpTilt_three_eq_cpPairTilt_one]
  simp [cpPairTilt]; norm_num

/-! ## Inclinação do 2-jato = sensibilidade transversal positiva -/

/-- A inclinação da fonte do tilt em `δ = 0` coincide com a primeira sensibilidade
transversal `carryTiltThreeFirstSensitivity`, pela unicidade da derivada. -/
theorem cpTiltThreeDeriv_zero_eq_sensitivity (c : ℝ) (hc : 1 < c) :
    cpTiltThreeDeriv c 0 = carryTiltThreeFirstSensitivity c :=
  (hasDerivAt_cpTilt_three c hc 0).unique (hasDerivAt_cpTilt_three_zero hc)

/-! ## O modelo quadrático (2-jato) e a fatoração `P·(1 − r)` -/

/-- 2-jato da fonte do tilt por célula: `L(c)·δ + ½·K(c)·δ²`. -/
def tiltCellQuadModel (c δ : ℝ) : ℝ :=
  carryTiltThreeFirstSensitivity c * δ + (1/2) * cpTiltThreeSecondDeriv c 0 * δ ^ 2

/-- Razão por célula `r_c(δ) = (-K(c)/(2L(c)))·δ`. -/
def tiltCellRatio (c δ : ℝ) : ℝ :=
  -cpTiltThreeSecondDeriv c 0 / (2 * carryTiltThreeFirstSensitivity c) * δ

/-- Ponto de virada da célula: `δ = 2L(c)/(-K(c))`. -/
def tiltCellCrossover (c : ℝ) : ℝ :=
  2 * carryTiltThreeFirstSensitivity c / (-cpTiltThreeSecondDeriv c 0)

/-- O 2-jato zera na linha (casa o valor da fonte real). -/
theorem tiltCellQuadModel_zero (c : ℝ) : tiltCellQuadModel c 0 = 0 := by
  unfold tiltCellQuadModel; ring

/-- Derivada do 2-jato em qualquer `δ`: `L(c) + K(c)·δ`. -/
theorem hasDerivAt_tiltCellQuadModel (c δ : ℝ) :
    HasDerivAt (fun x => tiltCellQuadModel c x)
      (carryTiltThreeFirstSensitivity c + cpTiltThreeSecondDeriv c 0 * δ) δ := by
  unfold tiltCellQuadModel
  have hlin : HasDerivAt (fun x : ℝ => carryTiltThreeFirstSensitivity c * x)
      (carryTiltThreeFirstSensitivity c) δ := by
    simpa using (hasDerivAt_id δ).const_mul (carryTiltThreeFirstSensitivity c)
  have hsq : HasDerivAt (fun x : ℝ => (1/2) * cpTiltThreeSecondDeriv c 0 * x ^ 2)
      (cpTiltThreeSecondDeriv c 0 * δ) δ := by
    have h := (hasDerivAt_pow 2 δ).const_mul ((1/2) * cpTiltThreeSecondDeriv c 0)
    refine h.congr_deriv ?_
    push_cast; ring
  refine (hlin.add hsq).congr_deriv ?_
  ring

/-- A inclinação do 2-jato em `δ = 0` é `L(c)` (casa a inclinação da fonte real). -/
theorem hasDerivAt_tiltCellQuadModel_zero (c : ℝ) :
    HasDerivAt (fun x => tiltCellQuadModel c x) (carryTiltThreeFirstSensitivity c) 0 := by
  simpa using hasDerivAt_tiltCellQuadModel c 0

/-- **Fatoração `P·(1 − r)`** do 2-jato por célula — a mesma forma da obstrução. -/
theorem tiltCellQuadModel_eq_slope_mul_one_sub_ratio (c δ : ℝ)
    (hL : carryTiltThreeFirstSensitivity c ≠ 0) :
    tiltCellQuadModel c δ = carryTiltThreeFirstSensitivity c * δ * (1 - tiltCellRatio c δ) := by
  unfold tiltCellQuadModel tiltCellRatio
  field_simp
  ring

/-- No ponto de virada a razão por célula vale `1`. -/
theorem tiltCellRatio_crossover (c : ℝ) (hL : carryTiltThreeFirstSensitivity c ≠ 0)
    (hK : cpTiltThreeSecondDeriv c 0 ≠ 0) :
    tiltCellRatio c (tiltCellCrossover c) = 1 := by
  unfold tiltCellRatio tiltCellCrossover
  have hKn : -cpTiltThreeSecondDeriv c 0 ≠ 0 := neg_ne_zero.mpr hK
  field_simp

/-! ## Sinais nos centros canônicos: `L > 0`, `K < 0`, virada positiva -/

/-- Em cada centro canônico a inclinação (orçamento) é positiva. -/
theorem canonicalCenter_budgetSlope_pos (k : ℕ) :
    0 < carryTiltThreeFirstSensitivity (canonicalRealCpCenter k) :=
  carryTiltThreeFirstSensitivity_pos (center_gt_one k)

/-- Para `k ≥ 1` o ponto de virada da célula é estritamente positivo. -/
theorem canonicalCenter_tiltCellCrossover_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < tiltCellCrossover (canonicalRealCpCenter k) := by
  unfold tiltCellCrossover
  have hL := canonicalCenter_budgetSlope_pos k
  have hK := canonicalCenter_cpTiltThreeSecondDeriv_zero_neg hk
  exact div_pos (by linarith) (by linarith)

/-- A razão por célula cresce e tende a `+∞` com `δ` (centros canônicos, `k ≥ 1`). -/
theorem canonicalCenter_tiltCellRatio_tendsto_atTop {k : ℕ} (hk : 1 ≤ k) :
    Tendsto (fun δ => tiltCellRatio (canonicalRealCpCenter k) δ) atTop atTop := by
  have hL := canonicalCenter_budgetSlope_pos k
  have hK := canonicalCenter_cpTiltThreeSecondDeriv_zero_neg hk
  have hslope : 0 < -cpTiltThreeSecondDeriv (canonicalRealCpCenter k) 0 /
      (2 * carryTiltThreeFirstSensitivity (canonicalRealCpCenter k)) :=
    div_pos (by linarith) (by linarith)
  have h := Filter.tendsto_id.const_mul_atTop hslope
  simpa [tiltCellRatio] using h

/-- **Virada por célula:** além do ponto de virada, o 2-jato da fonte do tilt é negativo
(centros canônicos, `k ≥ 1`). Análogo microscópico de `even_pivot_neg_iff_ratio_gt_one`:
a curvatura é o déficit que, acumulado, vence o orçamento `L(c)·δ`. -/
theorem canonicalCenter_tiltCellQuadModel_neg_after {k : ℕ} (hk : 1 ≤ k) {δ : ℝ}
    (hδ : tiltCellCrossover (canonicalRealCpCenter k) < δ) :
    tiltCellQuadModel (canonicalRealCpCenter k) δ < 0 := by
  have hL := canonicalCenter_budgetSlope_pos k
  have hK := canonicalCenter_cpTiltThreeSecondDeriv_zero_neg hk
  have hcross := canonicalCenter_tiltCellCrossover_pos hk
  have hδpos : 0 < δ := lt_trans hcross hδ
  have hslope : 0 < -cpTiltThreeSecondDeriv (canonicalRealCpCenter k) 0 /
      (2 * carryTiltThreeFirstSensitivity (canonicalRealCpCenter k)) :=
    div_pos (by linarith) (by linarith)
  have hmono : (1:ℝ) < tiltCellRatio (canonicalRealCpCenter k) δ := by
    have hone := tiltCellRatio_crossover (canonicalRealCpCenter k) hL.ne' hK.ne
    have hlt : tiltCellRatio (canonicalRealCpCenter k) (tiltCellCrossover (canonicalRealCpCenter k))
        < tiltCellRatio (canonicalRealCpCenter k) δ := by
      unfold tiltCellRatio
      exact mul_lt_mul_of_pos_left hδ hslope
    rwa [hone] at hlt
  rw [tiltCellQuadModel_eq_slope_mul_one_sub_ratio (canonicalRealCpCenter k) δ hL.ne']
  exact mul_neg_of_pos_of_neg (mul_pos hL hδpos) (by linarith)

/-- Antes do ponto de virada o 2-jato é positivo (orçamento vence): a célula ainda
"empurra pra cima" enquanto a razão fica abaixo de `1` (centros canônicos, `k ≥ 1`). -/
theorem canonicalCenter_tiltCellQuadModel_pos_before {k : ℕ} (hk : 1 ≤ k) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < tiltCellCrossover (canonicalRealCpCenter k)) :
    0 < tiltCellQuadModel (canonicalRealCpCenter k) δ := by
  have hL := canonicalCenter_budgetSlope_pos k
  have hK := canonicalCenter_cpTiltThreeSecondDeriv_zero_neg hk
  have hslope : 0 < -cpTiltThreeSecondDeriv (canonicalRealCpCenter k) 0 /
      (2 * carryTiltThreeFirstSensitivity (canonicalRealCpCenter k)) :=
    div_pos (by linarith) (by linarith)
  have hmono : tiltCellRatio (canonicalRealCpCenter k) δ < 1 := by
    have hone := tiltCellRatio_crossover (canonicalRealCpCenter k) hL.ne' hK.ne
    have hlt : tiltCellRatio (canonicalRealCpCenter k) δ
        < tiltCellRatio (canonicalRealCpCenter k) (tiltCellCrossover (canonicalRealCpCenter k)) := by
      unfold tiltCellRatio
      exact mul_lt_mul_of_pos_left hδ hslope
    rwa [hone] at hlt
  rw [tiltCellQuadModel_eq_slope_mul_one_sub_ratio (canonicalRealCpCenter k) δ hL.ne']
  exact mul_pos (mul_pos hL hδ0) (by linarith)

#print axioms cpTilt_three_zero
#print axioms cpTiltThreeDeriv_zero_eq_sensitivity
#print axioms tiltCellQuadModel_eq_slope_mul_one_sub_ratio
#print axioms canonicalCenter_tiltCellQuadModel_neg_after
#print axioms canonicalCenter_tiltCellQuadModel_pos_before

end
end CarryTiltSlice
