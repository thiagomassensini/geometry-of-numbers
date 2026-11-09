# Open obligations — radius-51 contour route

## Provenance invariant

All moments remain the original C2 moments:

`geometric bracket → Genuine → native scalar N → F=A*N → R=-F'/(2F) → completedSigmaLogJet 0 n → H_n → Hankel`.

The ten zeros only define the comparison power sums `P_n`; they never define or replace `F`, `R`, or `H_n`.

## Remaining checkpoints

- [x] C1: classify every zero of the original entire continuation in `|z|≤51`, prove the twenty listed roots simple using the count with multiplicity, and exclude zeros on `|z|=51`.
- [x] C2: normalize the original jets and prove the finite residue identity for every `n`; the Lean theorem gives the paired ten-mode formula and records the contour orientation and normalization without Hadamard factorization. See `C2_RESIDUE_REDUCTION.md`.
- [x] C3 external certificate: the full circle is rigorously bounded by `|R|<4/5` in the Arb interval certificate `C3_ARb_CERTIFICATE.md`, with all 512 arc enclosures in `evidence/C3_ARb_ARCS.csv`. This certificate is not formalized in Lean.
- [x] C4: the Lean theorem deriving the uniform `C=40` tail from a contour identity and the circle bound is complete. C2 now supplies the former as a theorem; the circle bound remains computer-assisted evidence, not a Lean input yet.
- [x] C5 external interval computation: rigorous Arb enclosures give positive rational lower margins for all six original-source residuals. Their inclusion in the Lean contour integrals remains open; do not treat the conditional hypothesis as discharged.
- [x] C6: the four exact rational strict margins and B1 large-order implication are proved in Lean. The generic gate keeps decomposition, scale boxes, tail, and signs explicit; the new source-level wrapper discharges the decomposition and boxes and leaves the circle bound and residual signs visible.

The new `SigmaContour51SourceTail.lean` specializes these generic results to the original completed
characteristic. It derives the source decomposition and scale boxes from the fixed C2 root list and
proves the all-window conclusion conditional only on the C3 circle norm bound and the six central
signs. Those Lean hypotheses are not discharged by the external Arb runs. `SigmaContour51BoxSensitivity.lean` now
formalizes the exact C5 source specialization at `d=0`: the displaced product is the square of
`completedNativeOperatorCharacteristic`, which equals the square of
`completedNativeCharacteristicContinuation` under the explicit genuine-strip condition; the source
log-derivative coefficients are `2*completedSigmaLogJet 0 n`, and `e_n` is half that source moment
minus the ten-mode power sum. This algebraic identity does not move any C5 interval enclosure from
`d=99/2000` or `d=1/10`; a quantitative displacement enclosure or a direct central source
evaluation is still required.

The same module proves the first-window gate `completedNative_sigmaPadeD_zero_pos_of_contour51_bound`:
once the circle bound is supplied, only `e_0≥0` and `e_2≥0` are required; `e_1` is bounded in
absolute value and no sign assumption on it is made. The minimal first-window inputs still to prove
from the original source using this route are therefore the Lean circle bound plus those two
residual signs. A second gate in `SigmaContour51ArbResidualGate.lean` is sharper for the available
certificate: it proves the first determinant from two-sided source intervals for `e_0,e_1,e_2`,
without a global circle bound. Its exact rational determinant margin is proved in Lean. A compiled
conditional adapter now transfers the 4096 arc table to those intervals; its universal
pointwise-inclusion premise remains open.

## Keep the three remainders distinct

The source residual is `e_n = H_n - P_n`, where `H_n` is the original completed C2 coefficient
and `P_n` is the exact ten-mode sum. The fixed-root Cauchy identity proves `H_n = P_n + e_n`,
with `e_n` represented by the normalized contour integral of the original logarithmic derivative.
The five determinant contributions stay together:

`D_s(H)-D_s(P) = P_s*e_(s+2) + e_s*P_(s+2) - 2*P_(s+1)*e_(s+1) + e_s*e_(s+2) - e_(s+1)^2`.

The material tail in the original C2 calculation is a separate object; no identity equating it to
`e_n` is used here. The Taylor/Cauchy remainder in the Arb arc evaluator only bounds the evaluator
on each parameter arc. It yields a bound for `e_n` only after pointwise inclusion is proved and the
complete arc ranges are integrated. The source decomposition, ten-mode residue contribution, and
evaluator remainder therefore cannot exchange bounds without these explicit identities and
transfers.

## Current mathematical limits

The older numerical contour and Taylor probes use 65-digit mpmath arithmetic and a finite mesh; they remain diagnostics only. Separate from them, C3 has rigorous external Arb certificates for the circle bound and two-sided intervals of the first six C2 residual integrals, with exact rational endpoints and positive lower margins in `C3_ARb_CERTIFICATE.md`. Lean checks the rational arithmetic of all six 4096 per-arc tables and compiles their conditional integration adapters; it does not yet prove the Arb-to-Lean evaluator inclusion. The exact open inputs are:

1. **Uniform circle bound:** prove in Lean that the 512-arc Arb enclosures imply `‖R z‖≤4/5` for every `‖z‖=51`, including validated Taylor/Cauchy remainders and their pointwise inclusion in the original response. `contour51OriginalResponse_eq_arb_formula_lower_path` now supplies the formal source evaluator on the lower semicircle; oddness handles the upper half. This is the `hR` input to C4.
2. **Six residual intervals:** prove `contour51ArbLowerPathResidualIntervalBounds`, namely the lower and upper rational endpoint inequalities for each original lower-path integral `n≤5`, from all 4096 complete-arc Arb ranges. The exact rational lists, all twelve weighted sums, and their comparisons with the stored aggregate endpoints are compiled for all six orders. `contour51ArbAllSixLowerPathResidualIntervalBounds_of_4096_arc_evaluator_inclusion` compiles the complete list-to-integral transfer, conditional on universal inclusion of the original evaluator in every closed-arc box, including its validated Taylor/Cauchy remainders. This pointwise inclusion for `n=0,…,5` and the separate 512-arc circle-bound transfer remain open.
3. **First unconditional advance:** prove the 4096-arc evaluator inclusion proposition for `n=0,1,2`. The compiled adapter then supplies `contour51ArbFirstThreeLowerPathResidualIntervalBounds`, and the existing determinant theorem gives the strict absolute margin `1/1000000000 < sigmaPadeD 0 0`.

The source differential identity and its explicit evaluator expansion are now compiled; `contour51OriginalResponse_eq_arb_formula_lower_path` proves the exact formula at every `u∈[0,1]`, with `F(z)≠0`, `0<Re(s)`, and `s≠1` discharged from C1 and the path geometry. Zeta nonvanishing follows from source nonvanishing and the exact factorization. The original full-circle parameterization, orientation, oddness/evenness, lower-path identity, and integrability are also compiled. The rational arithmetic and conditional integration of all six per-arc tables into the stored endpoint intervals are Lean theorems; the sole residual-transfer premise is the universal pointwise inclusion (including Taylor/Cauchy remainders). For all-window positivity, the Lean premises remain `hR` and all six residual intervals (equivalently the six signs in the separate source-tail theorem). The first-window gate uses the first three two-sided intervals, without `hR` or a sign premise on a remainder. C5 displaced boxes at nonzero `d` remain distinct; no Bernoulli table or full zeta/Gamma node certificate was duplicated.

The strict rational lower margins available for `e_0,…,e_5` are, respectively,
`9/1000`, `9/10000000`, `9/50000000000`, `1/25000000000000`,
`1/100000000000000000`, and `1/500000000000000000000`. Until the lower-path interval
proposition is proved from the Arb arc data, these are verified comparisons against external
endpoints, not Lean signs for `e_n`. The next minimal lemma for an unconditional first advance is
the pointwise 4096-arc evaluator inclusion for `n=0,1,2`, including its validated Taylor/Cauchy
remainder. The compiled adapter turns that universal inclusion into
`contour51ArbFirstThreeLowerPathResidualIntervalBounds`; the existing determinant gate then gives
`1/1000000000 < sigmaPadeD 0 0` without the global circle estimate. No current theorem asserts
that pointwise inclusion or unconditional positivity.

## Incremento compilado: redução semicircular para `hR`

`contour51ArbLowerSemicircleUniformResponseBound` nomeia a obrigação contínua
`∀ u∈[0,1], ‖R(circleMap 0 51 (-π*u))‖≤4/5`. O teorema
`contour51OriginalResponse_circle_norm_bound_of_lower_semicircle_uniform_bound` prova que essa
obrigação implica a cota em toda a esfera de raio 51, usando a periodicidade do parâmetro e a
paridade ímpar de `R=-F'/(2F)` para a continuação completada original `F`. Essa prova compila sem
hipóteses além da premissa semicircular e axiomas padrão do Lean.

O teorema não integra o certificado externo: a premissa universal ainda precisa ser demonstrada a
partir das 512 caixas completas de Arb, incluindo inclusão ponto a ponto da expressão original e
restos Taylor/Cauchy. Separadamente, permanece aberta a inclusão das 4096 caixas para os seis
integrandos residuais. A primeira meta mínima continua sendo a inclusão de `n=0,1,2`; isso basta
para o gate direto compilado de `1/1000000000 < sigmaPadeD 0 0`.

### Próximo bloco analítico verificável

O script C3 usa Taylor de ordem 32 para `ζ` e `ζ′` em cada arco, raio `1/4` e restos explícitos
por Cauchy; em seguida combina as caixas de `s`, `s-1`, `log π` e `digamma(s/2)` para limitar
`ζ′/ζ` e a resposta. O CSV C3 e o JSON residual atual armazenam os limites finais, mas não um
rastro racional das caixas dos coeficientes Taylor e das operações intermediárias que permita a
Lean verificar a inclusão da função. O menor novo certificado formal é uma inclusão de `ζ` e
`ζ′` sobre um arco completo, a partir de caixas racionais para os coeficientes e do majorante e
razão de Cauchy já descritos pelo script; depois combina-se essa caixa com as demais parcelas da
fórmula Lean. Para o primeiro avanço central, esse mecanismo precisa cobrir os 4096 arcos e
`n=0,1,2`; para `hR`, há a obrigação análoga nos 512 arcos.

### Fronteira de reutilização C5

Componentes reaproveitáveis sem refazer a certificação de C5: `SigmaFiniteRationalIntervals.lean`
e `SigmaFiniteRationalIntervalTransport.lean` fornecem aritmética racional de bolas reais,
contenção e transporte para somas/momentos; `SigmaC5RationalNodeEval.lean` fornece conversão e
contenção de pontos complexos racionais e reutiliza o tipo retangular `ComplexInterval`; e
`SigmaSourceBezout.lean` mais `SigmaContour51BoxSensitivity.lean` fornecem a recorrência da fonte,
normalização e especialização algébrica em `d=0`. `SigmaC5PiInterval.lean` fornece
`c5_pi_log_interval_contains`, e `SigmaContour51C5PiBridge.lean` prova que essa caixa real,
embutida numa caixa complexa retangular, contém exatamente `Complex.log (Real.pi : ℂ)`.

Os avaliadores C5 `c5RationalZetaNodeBox_contains` e
`c5RationalZetaCenteredNodeBox_contains` só certificam ζ em pontos racionais isolados próximos a
`0.5+0i` (`a∈[2/5,3/5]`, `b∈[0,128/100000]`); eles não certificam retângulos contínuos, ζ′ ou
coeficientes Taylor, e não cobrem o contorno de raio 51. Os certificados C5 de Gamma também são
valores em nós fixos e não dão uma caixa uniforme para `digamma(s/2)`. Assim, nenhuma tabela de
Bernoulli ou lista de nós zeta/Gamma foi refeita, e os nós C5 restantes exigiriam transformação
quantitativa dos centros/caixas. As caixas de `d=0.0495` e `d=0.1` também continuam sem transporte
quantitativo ao centro.

## Divisão intervalar complexa formalizada; enclosures analíticos ainda abertos

`SigmaContour51ComplexIntervalDivision.lean` prova que uma caixa retangular para `z`, outra para
`w`, e uma caixa racional positiva para `Complex.normSq w` produzem por `ComplexInterval.divBox`
uma caixa que contém `z/w`. Também prova a construção `normSqRange` a partir dos intervalos reais
e imaginários. A hipótese exata para o quociente é `denNormSq.contains (Complex.normSq w)` e
`0 < denNormSq.lo`; para derivar a positividade da caixa candidata, ainda é preciso verificar
racionalmente que `((ComplexInterval.normSqRange denBox).lo : ℝ)>0`.

Isso cobre apenas a soundness das operações de divisão. `SigmaContour51ArcGeometry.lean` agora
fornece caixas Lean contínuas para `s(u)` e o parâmetro do contorno nas partições de 4096 e 512
arcos; o bridge C5
para `log π` também compila. Continuam sem prova as caixas de `ζ(s(u))`, `ζ′(s(u))` e
`digamma(s(u)/2)`, as caixas de `normSq` para `s`, `s-1`, ζ e a potência `z^(2n+1)`, e a inclusão
do avaliador Lean nas faixas Arb. A fórmula combinadora pode usar quocientes sound sem axiomas
novos, mas nenhuma avaliação Arb é inferida desses dados e as hipóteses
`contour51Arb4096FirstThreeArcEvaluatorInclusion`,
`contour51Arb4096AllSixArcEvaluatorInclusion` e
`contour51Arb512ResponseArcEvaluatorInclusion` permanecem abertas.

## Composição da resposta formalizada; caixas por arco ainda não fornecidas

`SigmaContour51ArbIntervalComposition.lean` prova a composição da fórmula zeta/Gamma/digamma da
resposta original a partir de caixas dos componentes e a passagem do quociente residual por
`z^(2n+1)` para qualquer `n`. Seu registro `Contour51Arb4096N0ArcComponentBoxes` torna explícitos
os dados necessários no arco: caixas para `s`, zeta, zeta derivada, digamma, `log π` e o parâmetro;
limites positivos das normas quadradas dos denominadores; e inclusões de cada ponto do arco nessas
caixas. `SigmaContour51ArcGeometry.lean` fornece agora os campos `sContains` e
`parameterContains`; `SigmaContour51C5PiBridge.lean` fornece `logPiContains`. Para `n=0`, ainda
é necessário comparar os extremos da parte real da caixa composta com os extremos Arb de cada
arco; então o adaptador deriva a inclusão ponto a ponto.

Esse adaptador não fornece os registros. Não há ainda demonstração das caixas analíticas, das
normas quadradas positivas ou das comparações com os extremos; portanto, mesmo a inclusão completa
de ordem zero continua condicional. Os adaptadores por extremos `n=1,2` ainda não foram escritos.
O primeiro avanço determinantal segue dependendo das inclusões para `n=0,1,2`; o objetivo completo
segue dependendo das seis ordens residuais e da inclusão separada nos 512 arcos para `hR`.

## Incremento formal de Taylor/Cauchy — 2026-11-08

`SigmaContour51TaylorRemainder.lean` prova, para uma função holomorfa genérica e um disco com
majorante de fronteira `M`, os restos de Taylor usados pelo script C3. A razão `q` é uma entrada
verificável que satisfaz `‖z-c‖≤q*r` e `q<1`. Os restos são
`M*q^(N+1)/(1-q)` para o valor e
`(M/r)*q^N*((N+1)-N*q)/(1-q)^2` para a derivada. O módulo também verifica a propagação das
caixas dos coeficientes e do deslocamento pelo polinômio intervalar e a inflação por um erro
racional provado.

Para cada arco C3 ainda precisam ser fornecidos e provados:

1. Caixa racional para o centro e para todo deslocamento `s(u)-s₀` no arco, com
   `‖s(u)-s₀‖≤q*(1/4)` e `q<1`.
2. `DiffContOnCl` da zeta no disco de raio `1/4` e majorante de fronteira `M` derivado de
   caixas racionais. A checagem externa de que o disco evita o polo não é um teorema Lean.
3. Caixas racionais contendo os coeficientes exatos `deriv^k zeta(s₀)/k!`, para `k≤32`,
   incluindo a ligação das bolas `acb_series.zeta()` aos coeficientes verdadeiros. Uma tabela
   única basta: `SigmaContour51TaylorCoefficientBridge.lean` prova que o coeficiente de ζ′ no
   índice `k` é `(k+1)` vezes o coeficiente de ζ no índice `k+1`, e que a mesma tabela de caixas
   avalia o polinômio derivado. O resto Cauchy limita a cauda em relação ao Taylor exato; nem essa
   identidade nem o resto validam as caixas dos coeficientes.
4. Aplicar os restos para conter zeta e zeta′ no arco; conter separadamente `1/s`, `1/(s-1)`,
   `log π` e `digamma(s/2)`; provar que a caixa de zeta exclui zero; e então demonstrar a inclusão
   da resposta ou do integrando residual nas caixas Arb.
5. Só então usar a integração compilada: nos 4096 arcos para `n=0,1,2` para o primeiro avanço;
   nos seis índices para as seis margens; e nos 512 arcos em separado para obter `hR` e C4.

O novo módulo verifica a transformação “coeficientes + deslocamento + resto racional → caixa
contendo a função/derivada”, mas não descarrega esses inputs com os dados atuais. O resto do
avaliador continua distinto do resíduo de dez modos e da cauda material da C2; os cinco cruzamentos
do determinante permanecem inalterados.

## Uma tabela de Taylor para ζ e ζ′

`SigmaContour51TaylorCoefficientBridge.lean` compila a identidade exata
`contourTaylorCoefficient (deriv f) c k = (k+1) * contourTaylorCoefficient f c (k+1)`.
Com caixas dos coeficientes de `f` até `N`, a aritmética retangular derivada constrói uma caixa
para o polinômio de `deriv f` com `N` coeficientes; inflar por um erro derivativo provado contém
`deriv f z`. Isso espelha o uso de `acb_series.zeta()` no C3 e elimina a necessidade de certificar
uma tabela independente de coeficientes para ζ′.

O teorema `contourTaylorCauchyValueAndDerivativeBoxes` reúne esse transporte com os dois restos
de Cauchy: dadas analiticidade no disco, diferenciabilidade da derivada, majorante `M`, razão
`q<1`, cota do deslocamento, caixas de coeficientes e limites racionais acima dos dois restos,
ele conclui simultaneamente caixas para `f z` e `deriv f z`.

As hipóteses explícitas são: caixas dos coeficientes Taylor de `f` até `N`, caixa do deslocamento
`z-c` e limite racional para o resto Taylor de `deriv f`. Para obter esse resto por Cauchy,
continuam necessários `DiffContOnCl` de `f`, diferenciabilidade da derivada, majorante de fronteira
e `‖z-c‖≤q*r` com `0≤q<1`. Para ζ nos arcos atuais ainda não há prova das caixas exatas dos
coeficientes, dos majorantes dos discos ou do transporte dos centros Arb para os argumentos Lean.
Assim, essa ponte reduz os dados do avaliador, mas não descarrega as inclusões dos 512/4096 arcos.

## C3 — tabela racional e inclusão dos 512 arcos

`SigmaContour51ArbBoundCertificate512.lean` verifica em Lean os 512 limites superiores racionais
da coluna `response_upper`, todos abaixo de `746413/1000000<4/5`, e prova que os arcos fechados
da partição cobrem `[0,1]`. Sob `contour51Arb512ResponseArcEvaluatorInclusion`, isso produz a
cota uniforme no semicírculo e, pela simetria já provada, a cota em todo o círculo de raio 51.

A hipótese ainda não provada é a inclusão ponto a ponto da resposta da fonte original em cada
extremo Arb: para todo `k<512` e todo `u∈[k/512,(k+1)/512]`, provar
`‖R(circleMap 0 51 (-π*u))‖≤upper[k]`. Isso exige formalizar a avaliação zeta/Gamma/digamma e
os restos Taylor/Cauchy em todos os arcos. Em separado, as inclusões residuais de 4096 arcos
continuam abertas para `n=0,…,5`; a restrição `n=0,1,2` é o próximo lema mínimo para o primeiro
determinante. A composição com todas as janelas deixa os seis sinais `e_n≥0` explícitos.

`SigmaContour51Arb512ComponentComposition.lean` agora formaliza a implicação componente a
componente: se, em cada arco, forem provadas as caixas contínuas de `s`, ζ, ζ′, digamma e `log π`,
as normas quadradas positivas de `s`, `s-1`, ζ e uma comparação racional do `normBound` da caixa de
resposta com o endpoint Arb, então segue a inclusão nesse arco. A família dos 512 registros implica
`contour51Arb512ResponseArcEvaluatorInclusion`, que já alimenta o teorema condicional de `hR`.
`SigmaContour51ArcGeometry.lean` fornece as caixas geométricas `s(u)` e `z(u)` para esses 512
arcos; ainda não há caixas Lean de ζ/ζ′/digamma nem comparações verificadas para preencher os
registros. Portanto `hR` continua condicional.
