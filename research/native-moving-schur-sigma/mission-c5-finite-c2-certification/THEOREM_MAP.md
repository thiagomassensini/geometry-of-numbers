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

## C5 O3 — propagação racional e sinais condicionais PROVADOS

Arquivos novos:

- `research/native-moving-schur-sigma/SigmaFiniteRationalIntervals.lean`
- `research/native-moving-schur-sigma/SigmaFiniteRationalIntervalBoxes.lean`
- `research/native-moving-schur-sigma/SigmaFiniteRationalIntervalTransport.lean`
- `research/native-moving-schur-sigma/SigmaFiniteRationalIntervalSigns.lean`
- `research/native-moving-schur-sigma/SigmaFiniteRationalIntervalCertificates.lean`
- `research/native-moving-schur-sigma/SigmaFiniteRationalIntervalAudit.lean`

| Declaração | Status, hipóteses e conclusão |
|---|---|
| `sigmaRatBallContains_mul`, `sigmaRatBallContains_pow` | PROVADOS: aritmética exata das bolas racionais; a fórmula do raio inclui o termo produto dos raios. |
| `sigmaFiniteScaledMomentBall_contains_of_recurrence` | PROVADO: propaga enclosures através da recorrência polinomial sem divisão da sequência escalada C4. |
| `sigmaC00495Minor_lower_pos`, `sigmaC00495Minor_final_neg` | PROVADOS por aritmética racional fechada: menores positivos para `s<11` e menor negativo em `s=11`. |
| `sigmaC01Minor_lower_pos`, `sigmaC01Minor_final_neg` | PROVADOS: menores positivos para `s<9` e menor negativo em `s=9`. |
| `sigmaPadeD_signs_at_99_2000_of_source_boxes` | PROVADO CONDICIONALMENTE a `sigmaC00495SourceBoxes`; sinais transferidos ao `sigmaPadeD` original. |
| `sigmaPadeD_signs_at_1_10_of_source_boxes` | PROVADO CONDICIONALMENTE a `sigmaC01SourceBoxes`; sinais transferidos ao `sigmaPadeD` original. |

Build limpo Lean 4.32 e auditoria transitiva aprovada; apenas `propext`,
`Classical.choice`, `Quot.sound`. Evidência em
`mission-c5-finite-c2-certification/evidence/rational-boxes/VALIDATION.md`.
O3 foi integrada pela PR #167, merge `fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`.
A prova das hipóteses de caixa é O4 e não foi resolvida.

## C5 O4 — origem das caixas ainda ABERTA

A branch de pesquisa Momentos, commit `68c9b5f0a196289e28a8e5586146707d27df6b75`, contém as caixas e scripts. As verificações foram reproduzidas por frações racionais exatas e deram:

- `d=99/2000`: `+++++++++++-`;
- `d=1/10`: `+++++++++-`.

Os sinais condicionais estão provados em Lean por O3. Ainda falta provar que os coeficientes da fonte estão nas caixas JSON; a origem delas usa `mpmath.iv` ainda não certificado. Ver `SESSION_STATE.md` e `evidence/interval-certificate/`.

## O4 — infraestrutura formal encontrada; inclusão da fonte ainda ABERTA

Fontes existentes e recompiladas nesta etapa:

- `research/native-moving-schur-sigma/height50-certified/lean/ZetaLean/Rigor.lean`
- `research/native-moving-schur-sigma/height50-certified/lean/ZetaLean/IntervalExp.lean`
- `research/native-moving-schur-sigma/height50-certified/lean/ZetaLean/IntervalCExp.lean`

As inclusões `ZetaLean.Interval.contains_logQ`,
`ZetaLean.Interval.contains_expI`, `ZetaLean.ComplexInterval.contains_expC` e
`ZetaLean.ComplexInterval.contains_dirichletTerm` compilam em Lean 4.32 e foram
auditadas; somente `propext`, `Classical.choice`, `Quot.sound` aparecem.
Isso fornece avaliação certificada de `log`, `exp` e `m^{-s}`, mas ainda não
compõe os coeficientes C2.

`research/native-moving-schur-sigma/SigmaGammaEulerIntegral.lean` prova a
ponte da Gamma original à aproximação explícita de Euler
`gammaFinite 512 81 z` com erro `≤10⁻³²` (PR #171) e uma versão de alta precisão
`gammaFinite 1024 240 z` com erro `≤10⁻⁹⁹` (PR #173). O novo
build e auditoria de dez raízes usam apenas axiomas padrão (`propext`,
`Classical.choice`, `Quot.sound`).

A prova `gamma_finite_3072_620_error`, integrada pela PR #175, reduz o erro
uniforme para `10⁻²⁵⁹`, com auditoria de doze raízes. `SigmaRationalInterpolation.lean`
formaliza agora a identidade algébrica dos 129 nós: recupera exatamente
polinômios racionais de grau menor que 129 e expressa cada coeficiente como
soma ponderada das avaliações nodais. Os limites numéricos dos pesos e a
aplicação dessa identidade à fonte C2 ainda estão pendentes.

**Primeiro lema C5 O4 ainda ausente:** caixas racionais estreitas para
`gammaFinite 3072 620 z` nos valores racionais de `z` usados na interpolação.
A soma direta tem cancelamento grande; a ponte Euler de erro `10⁻²⁵⁹` já está
disponível. A alternativa `Zeta23.DigammaSeries.inv_gamma_eq_prod` continua
disponível. Depois será necessário certificar Hurwitz e compor Cauchy/Fourier
sem alterar a cabeça C2, a cauda exata ou a completação original.

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

## Identidade algébrica dos 129 nós — provada; limites O4 ainda abertos

Em `SigmaRationalInterpolation.lean`:

- `c5InterpolationNode_injOn` prova que os nós `j²` são distintos em `0≤j≤128`.
- `c5_interpolate_polynomial` prova a reconstrução exata de qualquer `p : ℚ[X]` com `degree p < 129` a partir das avaliações nodais.
- `c5InterpolationPolynomial_coeff` e `c5InterpolationPolynomial_coeff_of_degree_lt` dão a fórmula explícita dos coeficientes por somas de Lagrange.
- `c5InterpolationWeight` e `c5InterpolationWeightSum` representam os pesos escalados correspondentes a `t_j=j/100000`. `c5InterpolationWeightSum_zero_eq_one` prova que a soma absoluta de grau zero é `1`.
- Para grau um, `c5Coeff_one_eq_derivative_eval_zero` e `c5LagrangeBasis_derivative_eval_zero` dão a representação estrutural. `c5LagrangeBasisProductCoeffOne_bound` prova a cota por base; `c5InterpolationCoeffOneAbsSum_le_six` e `c5InterpolationWeightSum_one_lt_ten_eleven` fecham a soma escalada abaixo de `10^11`. Build limpo e auditoria de 21 raízes: `evidence/rational-boxes/degree1-weight-bound-validation.md`.
- Os limites de grau `2..14`, a cota analítica da fonte e a inclusão das caixas seguem abertos.

As quatorze raízes foram compiladas em Lean 4.32 e auditadas. Os comandos e hashes estão em `evidence/rational-boxes/VALIDATION.md` e `evidence/rational-boxes/source-and-olean-sha256.txt`. A expansão direta que excedeu o limite do simplificador está registrada em `interpolation-weight-degree1-prototype.log`.

**Limite de grau um — PROVADO E INTEGRADO:** os três teoremas acima foram
integrados pela PR #185; commit de prova `90a208df98e74a7c5ab1fe83a9ef0fc90c3d3cb6`,
merge `c840ba35711ac8f938fa24c191f2af60f505480d`. O build limpo Lean 4.32 e a
auditoria fail-closed de 21 raízes aceitam somente `propext`, `Classical.choice`
e `Quot.sound`. Evidência em `evidence/rational-boxes/degree1-weight-bound-validation.md`.
O resultado cobre somente grau um e não fecha O4; os graus `2..14` continuam
abertos.
