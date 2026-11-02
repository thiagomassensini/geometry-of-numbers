import CriticalConcavity
import OfflineObstruction
import AccumulationMechanism

/-!
# Decomposição `Q = P − D` do pivô da fonte real e a razão `R = D/P`

Este módulo realiza, **sobre o pivô genuíno `sourceSchur`** (não sobre um modelo de
brinquedo), a decomposição pedida na Seção D do REPORT: escrever a forma deformada
do pivô como orçamento positivo menos déficit, e dar o critério de obstrução pela
razão `R = D/P`.

A deformação algébrica usada é a já demonstrada em `SourceSchurShift`:
`sourceSchur (perturb c 5 d) false 2 = sourceSchur c false 2 − 5·c₀·d`,
isto é, o pivô é **afim** no deslocamento `d` do coeficiente `c₅`, com inclinação
`−5c₀`. Batizando

* orçamento (parte positiva)  `P := sourceSchur c false 2`;
* déficit do deslocamento     `D(d) := 5·c₀·d`;
* pivô deformado              `Q(d) := sourceSchur (perturb c 5 d) false 2`,

obtém-se `Q(d) = P − D(d)` exatamente, e, para `P > 0`, a fatoração

\[ Q(d) = P\,\bigl(1 - R(d)\bigr), \qquad R(d) = D(d)/P. \]

Esta é a **mesma forma algébrica** do modelo harmônico de `AccumulationMechanism`
(`‖v‖²(1 − δ²‖v‖²)`), agora no pivô real: o pivô vira negativo exatamente quando a
razão passa de `1`, ou seja, quando o déficit supera o orçamento.

Honestidade (o que continua aberto, Seção D): aqui `d` é o deslocamento de `c₅`
tratado como parâmetro livre. Falta a ponte física que prove que o déficit do
carrier/bordo/cauda fora da linha produz `d` grande o bastante (`R > 1`). Esta
decomposição fornece o **critério** `R > 1 ⟺ pivô < 0`; não demonstra que a fonte
física o atinge. Nenhum módulo anterior é modificado.
-/

namespace CarryTiltSlice
open CPFormal.Analytic.Cp CarrySelfAdjointOperator CarrySourceBezout CarrySourceDimensionThree
open Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Canal par: orçamento, déficit e pivô deformado -/

/-- Orçamento (parte positiva `P`): o pivô par base. -/
def evenSourceBudget (c : ℕ → ℝ) : ℝ := sourceSchur c false 2

/-- Déficit `D(d)`: o termo produzido pelo deslocamento `d` de `c₅` (inclinação `5c₀`). -/
def evenSourceDeficit (c : ℕ → ℝ) (d : ℝ) : ℝ := 5 * c 0 * d

/-- Razão de crescimento relativo `R(d) = D(d)/P`. -/
def evenSourceRatio (c : ℕ → ℝ) (d : ℝ) : ℝ := evenSourceDeficit c d / evenSourceBudget c

/-- Margem base: quanto `c₅` está abaixo do seu teto. -/
def evenSourceMargin (c : ℕ → ℝ) : ℝ := evenSourceCeiling c / (5 * c 0) - c 5

/-- **Decomposição `Q = P − D`.** O pivô deformado é o orçamento menos o déficit. -/
theorem even_deformed_pivot_eq (c : ℕ → ℝ) (d : ℝ) :
    sourceSchur (perturb c 5 d) false 2 = evenSourceBudget c - evenSourceDeficit c d := by
  unfold evenSourceBudget evenSourceDeficit
  rw [even_schur_shift]

/-- O pivô deformado é negativo sse o déficit supera o orçamento. -/
theorem even_pivot_neg_iff_deficit_gt_budget (c : ℕ → ℝ) (d : ℝ) :
    sourceSchur (perturb c 5 d) false 2 < 0 ↔ evenSourceBudget c < evenSourceDeficit c d := by
  rw [even_deformed_pivot_eq]; constructor <;> intro h <;> linarith

/-- O pivô deformado é positivo sse o déficit fica abaixo do orçamento. -/
theorem even_pivot_pos_iff_deficit_lt_budget (c : ℕ → ℝ) (d : ℝ) :
    0 < sourceSchur (perturb c 5 d) false 2 ↔ evenSourceDeficit c d < evenSourceBudget c := by
  rw [even_deformed_pivot_eq]; constructor <;> intro h <;> linarith

/-- **Fatoração `Q = P·(1 − R)`** — o análogo exato do modelo harmônico, agora no pivô real. -/
theorem even_pivot_eq_budget_mul_one_sub_ratio (c : ℕ → ℝ) (d : ℝ)
    (hP : evenSourceBudget c ≠ 0) :
    sourceSchur (perturb c 5 d) false 2 = evenSourceBudget c * (1 - evenSourceRatio c d) := by
  rw [even_deformed_pivot_eq, evenSourceRatio]
  field_simp

/-- **Critério de obstrução pela razão:** com orçamento positivo, o pivô é negativo
exatamente quando a razão relativa passa de `1`. -/
theorem even_pivot_neg_iff_ratio_gt_one (c : ℕ → ℝ) (d : ℝ) (hP : 0 < evenSourceBudget c) :
    sourceSchur (perturb c 5 d) false 2 < 0 ↔ 1 < evenSourceRatio c d := by
  rw [even_pivot_eq_budget_mul_one_sub_ratio c d hP.ne']
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  · intro h
    exact mul_neg_of_pos_of_neg hP (by linarith)

/-- Déficit vencendo orçamento (razão `> 1`) força pivô negativo: a obstrução deformada. -/
theorem even_deficit_beats_budget_obstructs (c : ℕ → ℝ) (d : ℝ)
    (hP : 0 < evenSourceBudget c) (hR : 1 < evenSourceRatio c d) :
    sourceSchur (perturb c 5 d) false 2 < 0 :=
  (even_pivot_neg_iff_ratio_gt_one c d hP).mpr hR

/-- A razão é estritamente crescente no deslocamento (orçamento positivo). -/
theorem even_ratio_strict_mono (c : ℕ → ℝ) (hc0 : 0 < c 0) (hP : 0 < evenSourceBudget c)
    {d₁ d₂ : ℝ} (h : d₁ < d₂) : evenSourceRatio c d₁ < evenSourceRatio c d₂ := by
  unfold evenSourceRatio evenSourceDeficit
  rw [div_lt_div_iff_of_pos_right hP]
  nlinarith

/-- O déficit tende a `+∞` com o deslocamento. -/
theorem even_deficit_tendsto_atTop (c : ℕ → ℝ) (hc0 : 0 < c 0) :
    Tendsto (fun d => evenSourceDeficit c d) atTop atTop := by
  have h : Tendsto (fun d : ℝ => (5 * c 0) * d) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop (mul_pos (by norm_num) hc0)
  simpa [evenSourceDeficit] using h

/-- A razão tende a `+∞` com o deslocamento (orçamento positivo). -/
theorem even_ratio_tendsto_atTop (c : ℕ → ℝ) (hc0 : 0 < c 0) (hP : 0 < evenSourceBudget c) :
    Tendsto (fun d => evenSourceRatio c d) atTop atTop := by
  have h := (even_deficit_tendsto_atTop c hc0).atTop_div_const hP
  simpa [evenSourceRatio] using h

/-- Para qualquer fonte base com `c₀ > 0`, existe deslocamento que vira o pivô negativo. -/
theorem even_exists_deficit_flips_pivot (c : ℕ → ℝ) (hc0 : 0 < c 0) :
    ∃ d : ℝ, sourceSchur (perturb c 5 d) false 2 < 0 := by
  refine ⟨(|evenSourceBudget c| + 1) / (5 * c 0), ?_⟩
  rw [even_deformed_pivot_eq]
  have h5 : (5 : ℝ) * c 0 ≠ 0 := ne_of_gt (mul_pos (by norm_num) hc0)
  have hd : evenSourceDeficit c ((|evenSourceBudget c| + 1) / (5 * c 0))
      = |evenSourceBudget c| + 1 := by
    unfold evenSourceDeficit; field_simp
  rw [hd]
  have := le_abs_self (evenSourceBudget c)
  linarith

/-- Orçamento positivo ⟺ a fonte base está estritamente sub-teto (margem positiva). -/
theorem even_budget_pos_iff_margin_pos (c : ℕ → ℝ) (hc : 0 < c 0) :
    0 < evenSourceBudget c ↔ 0 < evenSourceMargin c := by
  unfold evenSourceBudget evenSourceMargin
  rw [even_source_sign_iff c hc]
  constructor <;> intro h <;> linarith

#print axioms even_deformed_pivot_eq
#print axioms even_pivot_eq_budget_mul_one_sub_ratio
#print axioms even_pivot_neg_iff_ratio_gt_one
#print axioms even_ratio_tendsto_atTop

/-! ## Canal ímpar: mesma decomposição (inclinação `−6c₀`, coeficiente `c₆`) -/

/-- Orçamento ímpar `P`: o pivô ímpar base. -/
def oddSourceBudget (c : ℕ → ℝ) : ℝ := sourceSchur c true 2

/-- Déficit ímpar `D(d)`: deslocamento `d` de `c₆` (inclinação `6c₀`). -/
def oddSourceDeficit (c : ℕ → ℝ) (d : ℝ) : ℝ := 6 * c 0 * d

/-- Razão ímpar `R(d) = D(d)/P`. -/
def oddSourceRatio (c : ℕ → ℝ) (d : ℝ) : ℝ := oddSourceDeficit c d / oddSourceBudget c

/-- Margem ímpar base. -/
def oddSourceMargin (c : ℕ → ℝ) : ℝ := oddSourceCeiling c / (6 * c 0) - c 6

/-- Decomposição `Q = P − D` (ímpar). -/
theorem odd_deformed_pivot_eq (c : ℕ → ℝ) (d : ℝ) :
    sourceSchur (perturb c 6 d) true 2 = oddSourceBudget c - oddSourceDeficit c d := by
  unfold oddSourceBudget oddSourceDeficit
  rw [odd_schur_shift]

theorem odd_pivot_neg_iff_deficit_gt_budget (c : ℕ → ℝ) (d : ℝ) :
    sourceSchur (perturb c 6 d) true 2 < 0 ↔ oddSourceBudget c < oddSourceDeficit c d := by
  rw [odd_deformed_pivot_eq]; constructor <;> intro h <;> linarith

/-- Fatoração `Q = P·(1 − R)` (ímpar). -/
theorem odd_pivot_eq_budget_mul_one_sub_ratio (c : ℕ → ℝ) (d : ℝ)
    (hP : oddSourceBudget c ≠ 0) :
    sourceSchur (perturb c 6 d) true 2 = oddSourceBudget c * (1 - oddSourceRatio c d) := by
  rw [odd_deformed_pivot_eq, oddSourceRatio]
  field_simp

/-- Critério de obstrução pela razão (ímpar). -/
theorem odd_pivot_neg_iff_ratio_gt_one (c : ℕ → ℝ) (d : ℝ) (hP : 0 < oddSourceBudget c) :
    sourceSchur (perturb c 6 d) true 2 < 0 ↔ 1 < oddSourceRatio c d := by
  rw [odd_pivot_eq_budget_mul_one_sub_ratio c d hP.ne']
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  · intro h
    exact mul_neg_of_pos_of_neg hP (by linarith)

theorem odd_deficit_beats_budget_obstructs (c : ℕ → ℝ) (d : ℝ)
    (hP : 0 < oddSourceBudget c) (hR : 1 < oddSourceRatio c d) :
    sourceSchur (perturb c 6 d) true 2 < 0 :=
  (odd_pivot_neg_iff_ratio_gt_one c d hP).mpr hR

theorem odd_ratio_strict_mono (c : ℕ → ℝ) (hc0 : 0 < c 0) (hP : 0 < oddSourceBudget c)
    {d₁ d₂ : ℝ} (h : d₁ < d₂) : oddSourceRatio c d₁ < oddSourceRatio c d₂ := by
  unfold oddSourceRatio oddSourceDeficit
  rw [div_lt_div_iff_of_pos_right hP]
  nlinarith

theorem odd_ratio_tendsto_atTop (c : ℕ → ℝ) (hc0 : 0 < c 0) (hP : 0 < oddSourceBudget c) :
    Tendsto (fun d => oddSourceRatio c d) atTop atTop := by
  have h : Tendsto (fun d : ℝ => (6 * c 0) * d) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop (mul_pos (by norm_num) hc0)
  have hd : Tendsto (fun d => oddSourceDeficit c d) atTop atTop := by
    simpa [oddSourceDeficit] using h
  simpa [oddSourceRatio] using hd.atTop_div_const hP

theorem odd_exists_deficit_flips_pivot (c : ℕ → ℝ) (hc0 : 0 < c 0) :
    ∃ d : ℝ, sourceSchur (perturb c 6 d) true 2 < 0 := by
  refine ⟨(|oddSourceBudget c| + 1) / (6 * c 0), ?_⟩
  rw [odd_deformed_pivot_eq]
  have h6 : (6 : ℝ) * c 0 ≠ 0 := ne_of_gt (mul_pos (by norm_num) hc0)
  have hd : oddSourceDeficit c ((|oddSourceBudget c| + 1) / (6 * c 0))
      = |oddSourceBudget c| + 1 := by
    unfold oddSourceDeficit; field_simp
  rw [hd]
  have := le_abs_self (oddSourceBudget c)
  linarith

theorem odd_budget_pos_iff_margin_pos (c : ℕ → ℝ) (hc : 0 < c 0) :
    0 < oddSourceBudget c ↔ 0 < oddSourceMargin c := by
  unfold oddSourceBudget oddSourceMargin
  rw [odd_source_sign_iff c hc]
  constructor <;> intro h <;> linarith

#print axioms odd_deformed_pivot_eq
#print axioms odd_pivot_neg_iff_ratio_gt_one
#print axioms odd_exists_deficit_flips_pivot

end
end CarryTiltSlice
