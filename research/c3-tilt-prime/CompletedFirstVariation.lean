import TransverseLedger
import TiltLogDerivative

/-!
# Fechamento do elo: a variação transversal da característica completa em forma `T − D`

Eleva a estrutura `P − D` / razão (construída no toy, no pivô de Schur e na fonte por
célula) ao objeto físico de **quatro canais**: a primeira variação transversal real da
característica completa. Usa a decomposição **já demonstrada** no operador
(`completedNativeLogJetRealFirstVariation_eq_tilt_add_remainder`, empacotada em
`transverse_global_ledger`):

\[
  \Phi := \bigl(-\,\texttt{canonicalCompletedC3EnrichedTfvdLogJetTailReadout}(1/2)\bigr)_{\Re}
        = \underbrace{T}_{\text{tilt total}} + \underbrace{R}_{\text{resto carrier/cruzamentos}},
  \qquad 0 < T.
\]

Escrevendo o déficit `D := −R`, isto é exatamente a forma orçamento menos déficit,

\[ \Phi = T - D = T\,(1 - \rho), \qquad \rho = D/T, \]

a **mesma assinatura** `P·(1 − R)` dos três níveis anteriores — agora no objeto completo,
que já carrega carrier, cruzamentos, bordo, cauda e o multiplicador de completion. `Φ` é a
parte real de `−(leitura do log-jato TFVD completado)`, ou seja literalmente um readout
log-derivada do operador completado: a forma `−F'/(2F)` da observação do usuário aparece no
próprio objeto de quatro canais, e seu orçamento é o canal do tilt (positivo).

Honestidade: o **sinal** de `Φ` é a orientação transversal (REPORT A/C:
`transverse_sensitivity_positive`), NÃO o pivô de Schur. Ligar `Φ > 0` à positividade do
pivô (`sourceSchur`/`carrierCoefficient`) continua sendo a obrigação aberta da Seção D. O
que se fecha aqui é que a álgebra orçamento−déficit/razão vale no objeto completo, com o
mesmo orçamento positivo do canal do tilt. Nenhum módulo anterior é modificado.
-/

namespace CarryTiltSlice
open CarrySelfAdjointOperator CPFormal.Analytic.Cp
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- `Φ`: a primeira variação transversal (real) da característica completa. -/
def completedFirstVariation : ℝ :=
  (-canonicalCompletedC3EnrichedTfvdLogJetTailReadout (1/2:ℂ)).re

/-- Orçamento `T`: a sensibilidade total do canal do tilt. -/
def completedTiltBudget : ℝ := canonicalRealCriticalWeightedTiltTotalSensitivity

/-- Déficit `D := −R`: menos o resto carrier/cruzamentos. -/
def completedCarrierDeficit : ℝ := -canonicalRealCriticalCarrierRemainderTotalSensitivity

/-- Razão da obstrução completa `ρ = D/T`. -/
def completedObstructionRatio : ℝ := completedCarrierDeficit / completedTiltBudget

/-- O orçamento do tilt é positivo (importado do operador). -/
theorem completedTiltBudget_pos : 0 < completedTiltBudget :=
  canonicalRealCriticalWeightedTiltTotalSensitivity_pos

/-- **`Φ = T − D`** — a forma orçamento menos déficit na característica completa,
a partir da decomposição já demonstrada `Φ = T + R`. -/
theorem completed_firstVariation_eq_budget_sub_deficit :
    completedFirstVariation = completedTiltBudget - completedCarrierDeficit := by
  unfold completedFirstVariation completedTiltBudget completedCarrierDeficit
  rw [completedNativeLogJetRealFirstVariation_eq_tilt_add_remainder]
  ring

/-- `Φ > 0` sse o déficit carrier fica abaixo do orçamento do tilt. -/
theorem completed_firstVariation_pos_iff_deficit_lt_budget :
    0 < completedFirstVariation ↔ completedCarrierDeficit < completedTiltBudget := by
  rw [completed_firstVariation_eq_budget_sub_deficit]
  constructor <;> intro h <;> linarith

/-- **`Φ = T·(1 − ρ)`** — a fatoração `P·(1 − R)` no objeto completo de quatro canais. -/
theorem completed_firstVariation_eq_budget_mul_one_sub_ratio :
    completedFirstVariation = completedTiltBudget * (1 - completedObstructionRatio) := by
  rw [completed_firstVariation_eq_budget_sub_deficit, completedObstructionRatio]
  have hT : completedTiltBudget ≠ 0 := completedTiltBudget_pos.ne'
  field_simp

/-- `Φ > 0` sse a razão da obstrução completa fica abaixo de `1`. -/
theorem completed_firstVariation_pos_iff_ratio_lt_one :
    0 < completedFirstVariation ↔ completedObstructionRatio < 1 := by
  rw [completed_firstVariation_pos_iff_deficit_lt_budget, completedObstructionRatio,
    div_lt_one completedTiltBudget_pos]

/-- `Φ < 0` sse a razão da obstrução completa passa de `1` (o déficit vence o orçamento). -/
theorem completed_firstVariation_neg_iff_ratio_gt_one :
    completedFirstVariation < 0 ↔ 1 < completedObstructionRatio := by
  rw [completed_firstVariation_eq_budget_mul_one_sub_ratio]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · exact absurd h1 (not_lt.mpr completedTiltBudget_pos.le)
  · intro h
    exact mul_neg_of_pos_of_neg completedTiltBudget_pos (by linarith)

/-- Consistência com `transverse_global_ledger`: `Φ = T + R` com `0 < T`. -/
theorem completed_firstVariation_eq_ledger :
    completedFirstVariation
      = canonicalRealCriticalWeightedTiltTotalSensitivity
        + canonicalRealCriticalCarrierRemainderTotalSensitivity :=
  transverse_global_ledger.1

#print axioms completed_firstVariation_eq_budget_sub_deficit
#print axioms completed_firstVariation_eq_budget_mul_one_sub_ratio
#print axioms completed_firstVariation_pos_iff_ratio_lt_one
#print axioms completed_firstVariation_neg_iff_ratio_gt_one

end
end CarryTiltSlice
