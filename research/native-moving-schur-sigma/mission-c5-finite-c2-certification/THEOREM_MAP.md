# C5 — mapa dos teoremas e obrigações

## Fonte original e entradas C4

Arquivo integrado: `research/native-moving-schur-sigma/SigmaSourceBezout.lean`.

| Declaração | Status/contexto |
|---|---|
| `completedSigmaDisplacedSourceCoefficient` | Coeficiente real `cₙ(d)` da série-fonte construída a partir da densidade deslocada original. |
| `completedSigmaDisplacedMoment` | Sequência original `2*completedSigmaLogJet d n`; o fator 2 é parte da definição. |
| `completedSigmaDisplacedSourceSeries_mul_moments_eq_neg_derivative` | PROVADO: identidade formal C4 `C·H=-C′`. |
| `completedSigmaDisplacedSourceCoefficient_zero_pos` | PROVADO sob domínio de deslocamento C4: `c₀(d)>0`. |
| `completedSigmaDisplacedMoment_hankel_eq_two_sigmaMatrix` | PROVADO: Hankel original equivale a `2 • sigmaMatrix`. |

## C5 Fase 1 — transporte algébrico PROVADO

Arquivo novo: `research/native-moving-schur-sigma/SigmaFiniteCoefficientSignTransport.lean`.

| Declaração | Status, hipóteses e conclusão |
|---|---|
| `completedSigmaFiniteScaledMoment` | Define `pₙ=c₀^(n+1)·(2*completedSigmaLogJet d n)` a partir dos coeficientes/momentos C4 existentes. |
| `completedSigmaFiniteScaledMoment_recurrence` | PROVADO para `-(1/2)<d<1/2`: recorrência polinomial sem divisão. A soma usa `j+1` para `j∈range n`, os termos usuais `1≤j≤n`. |
| `completedSigmaFiniteScaledMoment_minor_identity` | PROVADO para todo `d,s`: `pₛpₛ₊₂−pₛ₊₁²=4c₀^(2s+4)·CarrySigmaPade.sigmaPadeD d s`. |
| `sigmaPadeD_pos_of_completedSigmaFiniteScaledMoment_minor_pos` | PROVADO sob domínio C4: transfere menor escalado positivo ao `sigmaPadeD` original usando `c₀>0`. |
| `sigmaPadeD_neg_of_completedSigmaFiniteScaledMoment_minor_neg` | PROVADO analogamente para sinal negativo. |

O fator `2` dos momentos está explícito em `completedSigmaDisplacedMoment`; por isso a identidade do menor tem fator `4`. Auditoria transitiva em `SigmaFiniteCoefficientSignTransportAudit.lean`: somente `propext`, `Classical.choice`, `Quot.sound`.

## C5 Fase 3 — sinais intervalares condicionais

A branch de pesquisa Momentos, commit `68c9b5f0a196289e28a8e5586146707d27df6b75`, contém as caixas e scripts. As verificações foram reproduzidas por frações racionais exatas e deram:

- `d=99/2000`: `+++++++++++-`;
- `d=1/10`: `+++++++++-`.

Esses sinais ainda não estão provados em Lean. Eles são condicionais à inclusão dos coeficientes nas caixas JSON. A origem das caixas usa `mpmath.iv` ainda não certificado; ver `SESSION_STATE.md` e `evidence/interval-certificate/`.

## Alvos finais C5 — ainda NÃO provados

As conclusões devem falar da sequência original e seus menores:

```lean
theorem completedSigma_first_negative_window_at_00495 :
  (∀ s ≤ 10, 0 < CarrySigmaPade.sigmaPadeD (99 / 2000 : ℝ) s) ∧
  CarrySigmaPade.sigmaPadeD (99 / 2000 : ℝ) 11 < 0

theorem completedSigma_first_negative_window_at_01 :
  (∀ s ≤ 8, 0 < CarrySigmaPade.sigmaPadeD (1 / 10 : ℝ) s) ∧
  CarrySigmaPade.sigmaPadeD (1 / 10 : ℝ) 9 < 0
```

A inclusão de `completedSigmaDisplacedSourceCoefficient d n` nas caixas racionais é o gate entre o cálculo condicional e esses teoremas incondicionais. Não usar uma sequência espectral, pencil ou modelo de polos como substituto.
