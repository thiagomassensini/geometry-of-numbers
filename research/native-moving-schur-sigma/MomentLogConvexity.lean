import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Núcleo analítico do Checkpoint B: cota de razão por log-convexidade

Lema geral, autocontido e reutilizável (independente da fonte sigma), que é o coração do
Checkpoint B da rota de construção do operador auto-adjunto limitado (GNS sem Hamburger):

Se `a : ℕ → ℝ` é não-negativa, **log-convexa** (`aₙ₊₁² ≤ aₙ·aₙ₊₂`) e tem **crescimento
exponencial controlado** (`aₙ ≤ C·(R²)ⁿ` com `R>0`), então `a₁ ≤ R²·a₀`.

Aplicado a `aₙ = L(X^{2n} p²)` (que é log-convexa por Cauchy–Schwarz da Hankel PSD, e
limitada exponencialmente por H2), isto dá exatamente `L(X²p²) ≤ R²·L(p²)` — a desigualdade
de multiplicação limitada. A instanciação à fonte (funcional `L` sobre `Polynomial ℝ`,
positividade de Hankel ⇒ `aₙ≥0` e log-convexidade, cota de Cauchy ⇒ H2) permanece a
formalizar; este arquivo entrega o núcleo matemático verificado.
-/

namespace CarryMomentLogConvex
open Filter
open scoped BigOperators Matrix
set_option autoImplicit false

/-- The finite Hankel matrix associated with a real sequence. -/
def hankelMatrix (h : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => h (i.val + j.val)

/-- A positive semidefinite Hankel matrix makes every finite polynomial-square
quadratic form nonnegative. This is the coefficient-vector form of H1 and does
not assume a measure or an operator representation. -/
theorem hankel_quadratic_nonneg {h : ℕ → ℝ} {N : ℕ}
    (hH : (hankelMatrix h N).PosSemidef) (c : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * h (i.val + j.val) := by
  have hq := hH.dotProduct_mulVec_nonneg c
  have heq : star c ⬝ᵥ (hankelMatrix h N *ᵥ c) =
      ∑ i, ∑ j, c i * c j * h (i.val + j.val) := by
    simp [dotProduct, Matrix.mulVec, hankelMatrix, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [heq] at hq
  exact hq

#print axioms hankel_quadratic_nonneg

/-- **Cota de razão por log-convexidade (núcleo do Checkpoint B).** Uma sequência
não-negativa log-convexa com crescimento exponencial limitado satisfaz `a₁ ≤ R²·a₀`.
Sem hipótese de positividade estrita dos termos. -/
theorem logConvex_expBounded_ratio {a : ℕ → ℝ} {C R : ℝ}
    (hpos : ∀ n, 0 ≤ a n)
    (hlogconv : ∀ n, a (n + 1) ^ 2 ≤ a n * a (n + 2))
    (hR : 0 < R)
    (hbound : ∀ n, a n ≤ C * (R ^ 2) ^ n) :
    a 1 ≤ R ^ 2 * a 0 := by
  -- Passo 1: monotonia da razão (sem divisão): `aₙ·a₁ ≤ aₙ₊₁·a₀`.
  have hcross : ∀ n, a n * a 1 ≤ a (n + 1) * a 0 := by
    intro n
    induction n with
    | zero => nlinarith [hpos 0, hpos 1]
    | succ n ih =>
      rcases eq_or_lt_of_le (hpos n) with h0 | hn
      · have hsq : a (n + 1) ^ 2 ≤ 0 := by
          have h := hlogconv n; rw [← h0, zero_mul] at h; exact h
        have han1 : a (n + 1) = 0 := by
          have : a (n + 1) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
          exact pow_eq_zero_iff (by norm_num) |>.mp this
        rw [han1, zero_mul]
        exact mul_nonneg (hpos (n + 2)) (hpos 0)
      · have key : a n * (a (n + 1) * a 1) ≤ a n * (a (n + 2) * a 0) := by
          nlinarith [mul_le_mul_of_nonneg_right ih (hpos (n + 1)),
            mul_le_mul_of_nonneg_right (hlogconv n) (hpos 0)]
        exact le_of_mul_le_mul_left key hn
  -- Passo 2: cota geométrica inferior: `a₀·a₁ⁿ ≤ aₙ·a₀ⁿ`.
  have hpow : ∀ n, a 0 * a 1 ^ n ≤ a n * a 0 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_right ih (hpos 1),
        mul_le_mul_of_nonneg_right (hcross n) (pow_nonneg (hpos 0) n),
        hpos 0, hpos 1, pow_nonneg (hpos 0) n]
  -- Passo 3: conclusão.
  rcases eq_or_lt_of_le (hpos 0) with h0 | h0
  · -- caso degenerado `a₀ = 0`: `a₁² ≤ a₀·a₂ = 0 ⇒ a₁ = 0`.
    have hsq : a 1 ^ 2 ≤ 0 := by
      have h := hlogconv 0; rw [← h0, zero_mul] at h; exact h
    have ha1 : a 1 = 0 := by
      have : a 1 ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
      exact pow_eq_zero_iff (by norm_num) |>.mp this
    rw [ha1, ← h0, mul_zero]
  · -- caso `a₀ > 0`: contradição exponencial se `a₁ > R²·a₀`.
    by_contra hcon
    rw [not_le] at hcon
    have hRa : 0 < R ^ 2 * a 0 := by positivity
    set r : ℝ := a 1 / (R ^ 2 * a 0) with hr_def
    have hr1 : 1 < r := by
      rw [hr_def, lt_div_iff₀ hRa, one_mul]; exact hcon
    have ha1 : a 1 = r * (R ^ 2 * a 0) := by
      rw [hr_def, div_mul_cancel₀ _ hRa.ne']
    have hb : ∀ n, a 0 * r ^ n ≤ C := by
      intro n
      have hub : a n * a 0 ^ n ≤ C * (R ^ 2 * a 0) ^ n := by
        have h1 : a n * a 0 ^ n ≤ C * (R ^ 2) ^ n * a 0 ^ n :=
          mul_le_mul_of_nonneg_right (hbound n) (pow_nonneg h0.le n)
        calc a n * a 0 ^ n ≤ C * (R ^ 2) ^ n * a 0 ^ n := h1
          _ = C * (R ^ 2 * a 0) ^ n := by rw [mul_pow]; ring
      have hchain : a 0 * a 1 ^ n ≤ C * (R ^ 2 * a 0) ^ n := le_trans (hpow n) hub
      have hexp : a 1 ^ n = r ^ n * (R ^ 2 * a 0) ^ n := by rw [ha1, mul_pow]
      rw [hexp] at hchain
      have hpos_pow : 0 < (R ^ 2 * a 0) ^ n := pow_pos hRa n
      have hfinal : (a 0 * r ^ n) * (R ^ 2 * a 0) ^ n ≤ C * (R ^ 2 * a 0) ^ n := by
        nlinarith [hchain]
      exact le_of_mul_le_mul_right hfinal hpos_pow
    have htend : Tendsto (fun n => a 0 * r ^ n) atTop atTop :=
      Tendsto.const_mul_atTop h0 (tendsto_pow_atTop_atTop_of_one_lt hr1)
    obtain ⟨n, hn⟩ := (htend.eventually_gt_atTop C).exists
    exact absurd (hb n) (not_le.mpr hn)

#print axioms logConvex_expBounded_ratio

end CarryMomentLogConvex
