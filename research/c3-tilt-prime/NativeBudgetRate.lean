import NativeProductTransport
import SourceRate

/-!
# Taxa explícita do orçamento de cauda literal completo

A taxa preexistente controla o erro final em norma. Aqui controlamos a própria
soma dos três orçamentos não negativos HT, TH e TT. A constante é obtida da
fonte original, sem sinal de pivô; não é avaliada numericamente neste módulo.
-/
namespace CarrySourceBezout
open CarryUniformSource CarrySelfAdjointOperator Filter Matrix
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem literal_full_budget_explicit_order_rate :
    ∃ C : ℝ, 0 < C ∧
      (∀ M n : ℕ, ‖literalTail M n‖ ≤ (C / ((M:ℝ)+1))*16^n) ∧
      ∀ (M r : ℕ) (b : Bool) (x y : Fin r → ℝ),
      literalErrorBudget M M b r x y ≤
      (4*(r:ℝ)^2*(2*sourceCoefficientMass r*sourceTailRadius C M r +
        3*(sourceTailRadius C M r)^2))*coordMass x*coordMass y := by
  obtain ⟨C,hC,henv⟩ := literal_tail_jet_envelope
  refine ⟨C,hC,henv,?_⟩
  intro M r b x y
  have hρ : 0 ≤ sourceTailRadius C M r := by unfold sourceTailRadius; positivity
  have hA : 0 ≤ sourceCoefficientMass r := sourceCoefficientMass_nonneg r
  have hh : ∀ k ≤ 2*r, ‖literalHead M k‖ ≤ sourceCoefficientMass r + sourceTailRadius C M r := by
    intro k hk
    exact head_bound_all_coefficients C hC henv M r k hk
  have ht : ∀ k ≤ 2*r, ‖literalTail M k‖ ≤ sourceTailRadius C M r := by
    intro k hk
    exact tail_bound_all_coefficients C hC henv M r k hk
  have h1 := directionalBudget_bound_order (literalHead M) (literalTail M) b r
    (sourceCoefficientMass r+sourceTailRadius C M r) (sourceTailRadius C M r)
    (add_nonneg hA hρ) hρ hh ht x y
  have h2 := directionalBudget_bound_order (literalTail M) (literalHead M) b r
    (sourceTailRadius C M r) (sourceCoefficientMass r+sourceTailRadius C M r)
    hρ (add_nonneg hA hρ) ht hh x y
  have h3 := directionalBudget_bound_order (literalTail M) (literalTail M) b r
    (sourceTailRadius C M r) (sourceTailRadius C M r) hρ hρ ht ht x y
  unfold literalErrorBudget
  calc
    _ ≤ (4*(r:ℝ)^2*(sourceCoefficientMass r+sourceTailRadius C M r)*sourceTailRadius C M r * coordMass x*coordMass y) +
        (4*(r:ℝ)^2*sourceTailRadius C M r*(sourceCoefficientMass r+sourceTailRadius C M r) * coordMass x*coordMass y) +
        (4*(r:ℝ)^2*sourceTailRadius C M r*sourceTailRadius C M r * coordMass x*coordMass y) := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

#print axioms literal_full_budget_explicit_order_rate
end
end CarrySourceBezout
