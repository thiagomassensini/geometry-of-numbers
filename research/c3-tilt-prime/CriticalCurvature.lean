import CriticalConcavity

/-!
# Fase B (curvatura) — a curvatura do tilt é negativa na linha

Prova que a curvatura por célula do tilt na linha autodual,
`cpTiltThreeSecondDeriv c 0 = (log(c−1))² + (log(c+1))² − 2(log c)²`,
é **estritamente negativa** para `c > e+1` (todos os centros canônicos `c_k ≥ 6`).

Mecanismo: `(log x)²` é estritamente côncava em `(e,∞)` (segunda derivada
`2(1−log x)/x² < 0`), logo sua segunda diferença centrada é negativa.

Honestidade: esta é a curvatura do **canal do tilt por célula**, não a curvatura
do coeficiente completo `c₅` (que ainda inclui carrier, cruzamentos, bordo e cauda,
com o jato de altura de ordem 10). O sinal líquido de `∂²_δ c₅` na linha, e sua
tradução ao deslocamento `d(δ)`, permanecem a obrigação física restante.

Não modifica nenhum módulo anterior.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem hasDerivAt_logSq {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (Real.log y) ^ 2) (2 * Real.log x * x⁻¹) x := by
  have hl : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  rw [show (fun y : ℝ => (Real.log y) ^ 2) = (fun y : ℝ => Real.log y * Real.log y) by
    funext y; ring]
  exact (hl.mul hl).congr_deriv (by ring)

theorem hasDerivAt_logSqDeriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => 2 * Real.log y * y⁻¹) (2 * (1 - Real.log x) * (x ^ 2)⁻¹) x := by
  have hl : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx.ne'
  refine ((hl.const_mul 2).mul hinv).congr_deriv ?_
  field_simp
  ring

theorem deriv2_logSq_neg {x : ℝ} (hx : Real.exp 1 < x) :
    deriv^[2] (fun y : ℝ => (Real.log y) ^ 2) x < 0 := by
  have hx0 : 0 < x := lt_trans (Real.exp_pos 1) hx
  have hlog : 1 < Real.log x := by
    have := Real.log_lt_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hev : deriv (fun y : ℝ => (Real.log y) ^ 2) =ᶠ[nhds x]
      (fun y : ℝ => 2 * Real.log y * y⁻¹) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Set.Ioi (0:ℝ) from hx0)] with y hy
    exact (hasDerivAt_logSq hy).deriv
  have hkey : deriv^[2] (fun y : ℝ => (Real.log y) ^ 2) x =
      2 * (1 - Real.log x) * (x ^ 2)⁻¹ := by
    rw [show (2:ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
      hev.deriv_eq, (hasDerivAt_logSqDeriv hx0).deriv]
  rw [hkey]
  have h1 : 2 * (1 - Real.log x) < 0 := by nlinarith
  have h2 : 0 < (x ^ 2)⁻¹ := by positivity
  exact mul_neg_of_neg_of_pos h1 h2

theorem strictConcaveOn_logSq :
    StrictConcaveOn ℝ (Set.Ioi (Real.exp 1)) (fun y : ℝ => (Real.log y) ^ 2) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi _) ?_ ?_
  · refine (Real.continuousOn_log.mono ?_).pow 2
    intro y hy
    exact ne_of_gt (lt_trans (Real.exp_pos 1) hy)
  · intro x hx
    rw [interior_Ioi] at hx
    exact deriv2_logSq_neg hx

/-- A curvatura por célula do tilt é estritamente negativa na linha, para centros
`c > e+1` (em particular todos os centros canônicos `c_k ≥ 6`). -/
theorem cpTiltThreeSecondDeriv_zero_neg {c : ℝ} (hc : Real.exp 1 + 1 < c) :
    cpTiltThreeSecondDeriv c 0 < 0 := by
  rw [cpTiltThreeSecondDeriv_zero]
  have hc1 : Real.exp 1 < c - 1 := by linarith
  have hc3 : Real.exp 1 < c + 1 := by linarith
  have hne : c - 1 ≠ c + 1 := by linarith
  have hmid := strictConcaveOn_logSq.2 (Set.mem_Ioi.mpr hc1) (Set.mem_Ioi.mpr hc3) hne
    (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (0:ℝ) < 1 / 2)
    (by norm_num : (1:ℝ) / 2 + 1 / 2 = 1)
  simp only [smul_eq_mul] at hmid
  rw [show (1:ℝ) / 2 * (c - 1) + 1 / 2 * (c + 1) = c by ring] at hmid
  nlinarith [hmid]

/-- Todos os centros canônicos `c_k = 3(k+1)` com `k ≥ 1` satisfazem `c_k ≥ 6 > e+1`,
logo a curvatura do tilt é negativa em cada célula (exceto, possivelmente, a primeira
célula `c₀ = 3`, caso de bordo onde `[c−1,c+1]` cruza `e`). -/
theorem canonicalCenter_cpTiltThreeSecondDeriv_zero_neg {k : ℕ} (hk : 1 ≤ k) :
    cpTiltThreeSecondDeriv (canonicalRealCpCenter k) 0 < 0 := by
  refine cpTiltThreeSecondDeriv_zero_neg ?_
  have h6 : (6:ℝ) ≤ canonicalRealCpCenter k := by
    unfold canonicalRealCpCenter
    have : (2:ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hk
    nlinarith
  have he : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  linarith

#print axioms cpTiltThreeSecondDeriv_zero_neg
#print axioms canonicalCenter_cpTiltThreeSecondDeriv_zero_neg

end
end CarryTiltSlice
