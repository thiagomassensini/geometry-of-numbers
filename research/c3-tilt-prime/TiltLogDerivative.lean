import TiltCurvatureBridge

/-!
# A razão da obstrução tem a forma log-derivada `−F'/(2F)` do operador completado

Observação estrutural: seja `F(δ) := ∂_δ (fonte do tilt por célula) = cpTiltThreeDeriv c δ`
a sensibilidade transversal como função de `δ`. Então

* `F(0) = L(c)` (o orçamento / primeira sensibilidade `carryTiltThreeFirstSensitivity`),
* `F'(0) = K(c)` (a curvatura `cpTiltThreeSecondDeriv c 0`).

Logo **`K` é literalmente a derivada-`δ` de `F`, cujo valor em `0` é `L`** — a segunda
derivada da fonte é a derivada da primeira. Substituindo na razão por célula da ponte,

\[
  r_c(\delta) = \frac{-K(c)}{2L(c)}\,\delta
             = -\frac{\delta}{2}\,\frac{F'(0)}{F(0)}
             = -\frac{\delta}{2}\,\bigl(\log F\bigr)'(0),
\]

isto é, a **mesma forma `−F'/(2F)`** da derivada logarítmica que governa o operador
completado (Hadamard / fórmula explícita). A direção da obstrução (`r_c` cresce) equivale
ao **sinal negativo da log-derivada da sensibilidade** `Λ(c) = F'(0)/F(0) = K/L < 0`.

Honestidade: aqui `F = ∂_δ cpTilt` é a sensibilidade do **canal do tilt por célula**, não a
característica completa `F(t) = V(t)[1+C_M+D_M+T_M]`. O que se demonstra é que a razão da
obstrução já tem, por célula, a assinatura `−F'/(2F)`. Identificar esse `F` com a derivada
logarítmica da característica completa continua sendo a obrigação física da Seção D.
Nenhum módulo anterior é modificado.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## `F(0) = L`, `F'(0) = K`: a curvatura é a derivada da sensibilidade -/

/-- `F'(0) = K(c)`: a curvatura é a derivada-`δ` da sensibilidade `F = ∂_δ fonte` em `0`. -/
theorem hasDerivAt_tiltSensitivity_zero (c : ℝ) (hc : 1 < c) :
    HasDerivAt (fun δ => cpTiltThreeDeriv c δ) (cpTiltThreeSecondDeriv c 0) 0 :=
  hasDerivAt_cpTiltThreeDeriv c hc 0

/-- **`K` é a derivada de `L`.** A curvatura `K(c)` é exatamente `F'(0)`, com `F(0) = L(c)`
(`cpTiltThreeDeriv_zero_eq_sensitivity`). -/
theorem curvature_eq_sensitivity_deriv (c : ℝ) (hc : 1 < c) :
    cpTiltThreeSecondDeriv c 0 = deriv (fun δ => cpTiltThreeDeriv c δ) 0 :=
  (hasDerivAt_tiltSensitivity_zero c hc).deriv.symm

/-! ## A razão por célula é `−(δ/2)·F'/F` -/

/-- Log-derivada da sensibilidade: `Λ(c) = F'(0)/F(0) = K(c)/L(c)`. -/
def tiltSensitivityLogDeriv (c : ℝ) : ℝ :=
  cpTiltThreeSecondDeriv c 0 / cpTiltThreeDeriv c 0

/-- **A razão por célula tem a forma log-derivada `−F'/(2F)`.** -/
theorem tiltCellRatio_eq_neg_half_logDeriv (c δ : ℝ) (hc : 1 < c) :
    tiltCellRatio c δ = -(δ / 2) * tiltSensitivityLogDeriv c := by
  have hL : carryTiltThreeFirstSensitivity c ≠ 0 := (carryTiltThreeFirstSensitivity_pos hc).ne'
  unfold tiltCellRatio tiltSensitivityLogDeriv
  rw [cpTiltThreeDeriv_zero_eq_sensitivity c hc]
  field_simp

/-! ## Sinal da log-derivada nos centros canônicos -/

/-- Nos centros canônicos (`k ≥ 1`) a log-derivada da sensibilidade é negativa:
`Λ(c_k) = K/L < 0`. É o que faz a razão da obstrução crescer. -/
theorem canonicalCenter_tiltSensitivityLogDeriv_neg {k : ℕ} (hk : 1 ≤ k) :
    tiltSensitivityLogDeriv (canonicalRealCpCenter k) < 0 := by
  unfold tiltSensitivityLogDeriv
  rw [cpTiltThreeDeriv_zero_eq_sensitivity _ (center_gt_one k)]
  exact div_neg_of_neg_of_pos
    (canonicalCenter_cpTiltThreeSecondDeriv_zero_neg hk)
    (canonicalCenter_budgetSlope_pos k)

/-- Nos centros canônicos a razão é `−(δ/2)·Λ(c_k)` com `Λ(c_k) < 0`: forma `−F'/(2F)`. -/
theorem canonicalCenter_tiltCellRatio_eq_neg_half_logDeriv {k : ℕ} (_hk : 1 ≤ k) (δ : ℝ) :
    tiltCellRatio (canonicalRealCpCenter k) δ
      = -(δ / 2) * tiltSensitivityLogDeriv (canonicalRealCpCenter k) :=
  tiltCellRatio_eq_neg_half_logDeriv _ δ (center_gt_one k)

/-- O ponto de virada é `δ = −2/Λ(c)`: puramente a log-derivada da sensibilidade. -/
theorem canonicalCenter_tiltCellCrossover_eq_neg_two_div_logDeriv {k : ℕ} (hk : 1 ≤ k) :
    tiltCellCrossover (canonicalRealCpCenter k)
      = -2 / tiltSensitivityLogDeriv (canonicalRealCpCenter k) := by
  have hLne : carryTiltThreeFirstSensitivity (canonicalRealCpCenter k) ≠ 0 :=
    (canonicalCenter_budgetSlope_pos k).ne'
  have hKne : cpTiltThreeSecondDeriv (canonicalRealCpCenter k) 0 ≠ 0 :=
    (canonicalCenter_cpTiltThreeSecondDeriv_zero_neg hk).ne
  unfold tiltCellCrossover tiltSensitivityLogDeriv
  rw [cpTiltThreeDeriv_zero_eq_sensitivity _ (center_gt_one k)]
  field_simp

#print axioms curvature_eq_sensitivity_deriv
#print axioms tiltCellRatio_eq_neg_half_logDeriv
#print axioms canonicalCenter_tiltSensitivityLogDeriv_neg
#print axioms canonicalCenter_tiltCellCrossover_eq_neg_two_div_logDeriv

end
end CarryTiltSlice
