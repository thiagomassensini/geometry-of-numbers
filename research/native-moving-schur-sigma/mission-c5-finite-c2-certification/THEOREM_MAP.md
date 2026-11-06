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

## C5, decomposição a formalizar

Definir uma recorrência genérica sem duplicar fonte/momentos:

```text
ell_n = 2 * completedSigmaLogJet d n
p_n = c_0^(n+1) * ell_n
p_0 = -c_1
p_n = -(n+1)c_(n+1)c_0^n - Σ_{j=1}^n c_j p_(n-j)c_0^(j-1)
```

Provar para todo `n`, por coeficientes da identidade C4, e provar:

```text
p_s*p_(s+2) - p_(s+1)^2
  = 4*c_0^(2*s+4) * sigmaPadeD d s
```

Com `c₀>0`, transferir sinais em ambas as direções. As conclusões finais devem usar os `sigmaPadeD` existentes:

```lean
theorem completedSigma_first_negative_window_at_00495 :
  (∀ s ≤ 10, 0 < sigmaPadeD (99 / 2000 : ℝ) s) ∧
  sigmaPadeD (99 / 2000 : ℝ) 11 < 0

theorem completedSigma_first_negative_window_at_01 :
  (∀ s ≤ 8, 0 < sigmaPadeD (1 / 10 : ℝ) s) ∧
  sigmaPadeD (1 / 10 : ℝ) 9 < 0
```

## Evidência condicional existente em Momentos

Branch remota `research/sigma-pade-dimension-depth-20261104`, inventário feito no commit `68c9b5f`:

- `investigations/c2_first_negative_interval_certificate_20261106/coeff_box_d00495_25digits.json`;
- `investigations/c2_first_negative_interval_certificate_20261106/coeff_box_d01_25digits.json`;
- `verify_signs_exact.py` opera sobre frações exatas e valida somente os sinais condicionados às caixas;
- `c2_em_interval.py` e `certify_finite_c2.py` calculam as caixas por operações elementares intervalares externas e alegam restos analíticos explícitos. Essa implementação ainda não é um verificador formal independente.

## Resultado final: sem declarações C5 ainda

Nenhum teorema Lean C5 foi criado nesta branch no checkpoint inicial. As inclusões
`completedSigmaDisplacedSourceCoefficient d n ∈ [lo,hi]` são o gate para elevar as provas
condicionais de sinal a conclusões da fonte original. Não usar sequência espectral, pencil ou
modelo de polos como conclusão.
