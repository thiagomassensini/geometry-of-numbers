# C5 — validação

## Avaliador racional genérico de zeta — PROVADO CONDICIONALMENTE

O build limpo de `SigmaC5RationalNodeEval.lean` e
`SigmaC5RationalNodeEvalAudit.lean` passou em Lean 4.32, com warnings como
erros. A auditoria de dez teoremas encontrou somente `propext`,
`Classical.choice` e `Quot.sound`; o checker fail-closed passou. A fatorização
de `emZetaHighRHS 100 300` mantém a soma de cauda explícita, e
`c5RationalZetaNodeBox_contains` inclui zeta sob condições explícitas do
avaliador `logQ`/`expCr`, inflando pela cota `<10^-250`.

Checkpoint integrado pela PR #207: commit de prova
`fb8bb31ed1fcbb4d1d9c88aceea1dd83539935df`, merge na `main`
`27a61e6bebcce178b81b961f507400ed77b96d3b`. Essa integração não altera os
limites de validação abaixo.

As condições de intervalo continuam sem instanciação concreta nos 129 nós.
Este checkpoint não calcula caixas para Gamma ou para a fonte C2 e não prova
as inclusões dos coeficientes nas caixas O3. Logs, pins, hashes e falha do
primeiro comando de reprodução estão em
`evidence/rational-boxes/c5-rational-node-evaluator-validation.md`.

## Reprodução das três caixas intervalares — PASSOU, condicional

As três configurações prescritas foram executadas novamente em uma cópia
temporária do checkout Momentos; o checkout compartilhado permaneceu sem
alterações. A cópia usou o patch preservado `momentos-gmpy2-compat.patch`, que
normaliza `gmpy2.mpz` para `int` antes de passar numeradores e denominadores a
`Decimal`. Todas as gerações terminaram com `REPRO_EXIT=0`. O verificador
independente por frações racionais exatas também passou nas três saídas, com
`+++++++++++-` nas duas configurações `d=0.0495` e `+++++++++-` em `d=0.1`.

Logs de geração: `sign1024_stirling-reproduced.log`,
`sign512_stirling_L12-reproduced.log` e `sign512_d01_L12-reproduced.log`.
Logs da checagem exata: os arquivos `*.exact-check.log` com os mesmos prefixos.
JSONs gerados e resultados exatos estão na mesma pasta. A falha anterior de
compatibilidade ficou registrada em `sign1024_stirling-initial-gmpy2-failure.log`;
as três tentativas iniciais sem patch nesta retomada encontraram a mesma falha
antes de escrever JSON. O registro completo, comandos e checksums estão em
`evidence/interval-certificate/reproduction-2026-11-06.md` e
`evidence/interval-certificate/reproduction-2026-11-06-sha256.txt`.

**Limite:** isso confirma sinais racionais condicionais aos intervalos
produzidos pela biblioteca experimental `mpmath.iv`. Não é uma prova formal de
que os coeficientes da fonte C2 original pertençam às caixas, portanto não
fecha O4 nem C5.

## Ponte Gamma de núcleo racional — build, auditoria e merge da PR #198

`SigmaC5GammaRationalCore.lean` define uma soma finita exata em `ℚ+iℚ` e prova
que `gammaFinite N T (a+bi)` é seu produto por `T^(a+bi)`. A caixa racional
exata contém esse núcleo; `gammaFiniteInterval_contains` combina-a com
`ZetaLean.ComplexInterval.dirichletTermBox2` para o fator de potência. Para
`N=3072`, `T=620`, `gamma3072Interval_contains` infla a caixa da Gamma finita
pelo erro rigoroso `10^-259` e inclui `Complex.Gamma (a+bi)`, sob as hipóteses
de intervalo e limite exponencial declaradas no teorema.

O build focado usa Lean `4.32.0`, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997` e Carry
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`; os módulos de apoio são
`SigmaGammaEulerIntegral` (erro `10^-259`, PR #175) e
`ZetaLean.IntervalCExp` (infraestrutura O4, PR #169). Ambos os módulos-alvo
foram compilados em diretório de saída limpo, com warnings como erros. O
checker fail-closed aceitou seis raízes, totalizando 11 relatórios dos dois
builds, e somente `propext`, `Classical.choice` e `Quot.sound`.

O commit de prova `a1646a1837603aee7d03384016ae514a7f7c820a` foi integrado
pela PR #198; o merge na `main` é `36cba9d805bc3274538cdc93bd0a3702154edcb2`.
O GitHub não reportou checks hospedados. Este merge não fecha O4/C5.

Logs: `c5-gamma-rational-core-try5-build.log`,
`c5-gamma-rational-core-audit-try6-build.log` e
`c5-gamma-rational-core-final-axiom-check.log`. Hashes de fonte, checker e
olean em `c5-gamma-rational-core-source-olean-sha256.txt`. O comando reprodutor
está nesta validação; o runner impõe `MemAvailable≥30 GiB`.

```bash
C5_SOURCE_ROOT="$PWD/research/native-moving-schur-sigma"
C5_EVIDENCE="$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes"
C5_OUTPUT="$PWD/.lake/build/research/native-moving-schur-sigma/c5-gamma-rational-core-final-clean-20261106"
C5_EULER_CACHE="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-gamma-euler-3072-clean"
C5_INTERVAL_CACHE="/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals-clean"
export SIGMA_REFERENCE_ROOT="/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105"
export CARRY_LEAN_ROOT="/home/thlinux/worktrees/carry-sigma-c2-pinned-045369"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT"
export SIGMA_HEIGHT50_BUILD="$C5_EULER_CACHE:$C5_INTERVAL_CACHE"
export LEAN_BIN="$(elan which lean)"
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5GammaRationalCore
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaC5GammaRationalCoreAudit
python3 "$C5_SOURCE_ROOT/check_c5_gamma_rational_core_axioms.py" \
  "$C5_EVIDENCE/c5-gamma-rational-core-try5-build.log" \
  "$C5_EVIDENCE/c5-gamma-rational-core-audit-try6-build.log"
```

**Limite desta etapa:** o teorema é genérico; não foram obtidos ainda valores
racionais efetivos para qualquer um dos 129 nós, nem a caixa completa da fonte
C2 nos pontos. A inclusão dos coeficientes nas caixas O3 continua não provada,
e C5 não está concluída.

## Avaliação da fonte C2 nos nós — ainda sem validação

A auditoria da rota confirma a reescrita exata da característica original para
`riemannZeta` e identifica `HardyFirstZero.zeta_em4_error` como o melhor resto
formal de Euler–Maclaurin encontrado na revisão pinada. Ele é de ordem 4 e sua
precisão em `N=100` não basta para incluir os coeficientes nas caixas O3. Ainda
faltam um resto de ordem alta para zeta/Hurwitz, sua avaliação em intervalos
Lean e a avaliação racional intervalar de `gammaFinite 3072 620`. Nenhuma caixa
de coeficiente foi validada por este diagnóstico. Detalhes e pins em
`evidence/rational-boxes/c5-original-source-zeta-route-audit.md`.

## Faixa racional exata de π — PASSOU e integrada pela PR #193

`SigmaC5PiBounds.lean` prova o erro da série alternada de `Real.arctan` para
argumentos racionais entre zero e um. Com truncações `N=170` e `N=55`, a
identidade de Machin dá `c5_pi_rational_enclosure`, que limita
`|Real.pi - c5PiCenter|` pelo racional exato `c5PiError`. O resultado não
depende da tentativa auxiliar de reduzir esse erro a uma potência decimal.

Build Lean 4.32 limpo com warnings como erros passou; a auditoria transitiva de
`c5_arctan_partial_enclosure` e `c5_pi_rational_enclosure` encontrou somente
`propext`, `Classical.choice` e `Quot.sound`. Logs, pins, hashes e comando estão
em `evidence/rational-boxes/c5-pi-bounds-validation.md`.

Merge na `main`: `2567ab0204c46c4ce04fca601c99e47e810e18b9`.

Esse incremento não certifica a avaliação da fonte nos nós e não prova
inclusão C2 nas caixas; C5 segue incompleta.

## `log π` e fator exponencial da completação — PASSOU e integrado pela PR #195

`SigmaC5PiInterval.lean` usa a faixa de π integrada pela PR #193 para provar
uma caixa racional de `Real.log Real.pi` por meio de `ZetaLean.Interval.log1`.
`SigmaC5PiExp.lean` transporta essa caixa pelo fator `-s/2` e aplica o
`ComplexInterval.expCr` já certificado para incluir o exponencial usado pela
definição original da completação.

Build limpo Lean 4.32 e auditoria das cinco raízes passaram; somente
`propext`, `Classical.choice` e `Quot.sound` aparecem. PR #195, commit de prova
`321ae94`, merge na `main` `0032b10295bfeaadb29d0387f9b99dde9b160ac3`.
Evidência reproduzível, pins e hashes em
`evidence/rational-boxes/c5-pi-completion-factor-validation.md`. O incremento
não avalia Gamma, a cauda C2 nem os 129 nós.

## Cota do módulo da fonte original — PASSOU e integrada; O4 parcial

`SigmaC5AnalyticBounds.lean` prova a cota uniforme
`CarrySigmaObstruction.displacedProductC_norm_le_10pow13_on_ball_39` para o
produto deslocado original, com `|d|≤1/10` e `z∈ball(0,39/100)`. A prova
mantém a característica nativa completada e seus fatores originais. Ela usa
uma cota da característica de `2·10^6` em cada fator; o produto fica abaixo
de `10^13`. Para a estimativa de Cauchy, usamos o contorno exterior de raio
`38/100`; seu disco fechado está estritamente dentro da bola aberta de raio
`39/100` na qual o lema da cota vale, e dentro do disco analítico aberto de
raio `2/5` integrado pela PR #189.

O build limpo em Lean 4.32 terminou com `BUILD_EXIT=0` e a cota `10^13` foi
integrada pela PR #192, merge `654dbb0bd7bb7d400cf0c4cab61bea1873995db4`. A auditoria
fail-closed das duas cotas Gamma, da cota `10^13` e do wrapper `10^100`
aceitou apenas `propext`, `Classical.choice` e `Quot.sound`. Logs, hashes e
detalhes estão em `evidence/rational-boxes/analytic-bounds-10pow13-validation.md`.

A análise de interpolação refeita em frações exatas com majorante `10^13` e
raio externo `38/100` confirma cauda `<10^-501` e erro Gamma amplificado
`<10^-135`. Isso ainda não certifica avaliações nos nós: O4 permanece aberta
até incluir os valores originais nos 129 pontos e provar as caixas dos
coeficientes C2.

## Limite de peso de grau um — PASSOU em build limpo e auditoria

`SigmaRationalInterpolation.lean` compila integralmente em Lean 4.32, em
diretório de saída limpo. Os teoremas
`c5LagrangeBasisProductCoeffOne_bound`,
`c5InterpolationCoeffOneAbsSum_le_six` e
`c5InterpolationWeightSum_one_lt_ten_eleven` concluem o limite escalado
`<10^11` do coeficiente de grau um.

A auditoria fail-closed percorreu 21 raízes, incluindo os três resultados
novos, e aceitou somente `propext`, `Classical.choice` e `Quot.sound`.
O checker não encontrou placeholder, axioma próprio ou `native_decide`.
Logs, hashes, pins e comandos:
`evidence/rational-boxes/degree1-weight-bound-validation.md`.

Este resultado é parcial: os graus `2..14`, a cota da fonte, as avaliações
racionais nos pontos e a inclusão dos coeficientes C2 nas caixas seguem
pendentes.

## Histórico de tentativas incompletas de grau um — 2026-11-06

Essas falhas são históricas e foram sucedidas pelo build limpo e pela auditoria
aprovada acima; permanecem para preservar a trilha de diagnóstico.

As tentativas abaixo foram **superadas pela validação limpa acima**. O módulo de produção havia sido estendido com
uma tentativa simbólica de `c5LagrangeBasisProductCoeffOne_bound` e corolários,
mas nenhuma compilação integral produziu `SigmaRationalInterpolation.olean`.
As tentativas, os perfis e os traces estão registrados em
`evidence/rational-boxes/c5-interpolation-degree1-*.log*`.

O lema auxiliar `c5_inv_sq_sum_range_le_isolated` compilou isoladamente em
Lean 4.32 (`c5-sum-bound-isolated-build.log`); isso não prova o limite do peso.
O último perfil integral elaborou o lema da soma, mas os lemas de produto
seguintes continuam sem conclusão. A saída rejeitada que encontrou axiomas
próprios gerados por `native_decide` está em
`interpolation-audit-degree1-native-decide-rejected.log`. O relatório
`interpolation-audit.log` restaurado é o histórico aprovado das 14 raízes da
versão anterior e não audita as raízes novas do checker atualizado.

A revisão WIP está na branch `codex/c5-degree1-weight-bound-20261106`, sobre
`origin/main` `c736dc073091e6184dbb673b622b6b91759accac`. O comando de retomada e
os pins estão em `RESTART_HERE.md` e
`evidence/rational-boxes/degree1-retry-checkpoint.md`.

**Estado das fases anteriores:** Fase 1 de transporte algébrico integrada pela PR #165. O3 foi integrada pela PR #167. A infraestrutura O4 e as pontes Euler-Gamma estão registradas nas PRs #169–#175; a interpolação, o peso constante e a estrutura derivativa de grau um nas PRs #177–#181. A prova `gamma_finite_3072_620_error` tem erro `≤10⁻²⁵⁹`, build Lean 4.32 e auditoria de doze raízes. A O4 continua aberta: faltam limites para graus `2..14`, a cota analítica da fonte e as inclusões C2.
**Toolchain:** `leanprover/lean4:v4.32.0`; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
**Base geometry da PR #165:** `91a1af2f9663d6761a3320e2f06504fe8aaa6776`; `main` após o merge: `75691edf0e74cc643f098213f60b684476132175`.
**Fonte C4 compilada:** source hashes de `SigmaSourceBezout.lean`, `SourceBezout.lean`, `SigmaPadeCorrespondence.lean` e `SigmaZeroObstruction.lean` conferem com `origin/main`; pins completos em `evidence/pins-and-sha256.txt`.

**O4, auditoria de 2026-11-06:** os módulos de intervalo elementar foram recompilados e auditados; também foi localizada a identidade formal de Weierstrass `Zeta23.DigammaSeries.inv_gamma_eq_prod`. Nenhuma caixa numérica para `Complex.Gamma` foi ainda derivada dessa identidade, e a aproximação Stirling usada pelo avaliador segue sem ponte Lean. O4 e a inclusão incondicional das caixas continuam abertas.

**Estado histórico após PR #181/#182:** a estrutura derivativa estava integrada, enquanto o limite numérico ainda aguardava prova.

**O4, prova Euler-Gamma de precisão alta integrada pela PR #173:** `gamma_finite_1024_240_error` aproxima a Gamma original por `gammaFinite 1024 240 z` com erro `≤10⁻⁹⁹` para `1495/20000≤Re(z)≤1`. Build Lean 4.32 e auditoria de dez raízes passaram; a caixa racional estreita da expressão finita continua pendente. Prova, logs e hashes estão em `evidence/rational-boxes/`.

## Estado após PR #185 — peso de grau um integrado

A PR #184 preservou o checkpoint incompleto (`5528ddc8093a22682c87f3f9c6575e30e90a7011`); a prova de grau um foi depois integrada pela PR #185, merge `c840ba35711ac8f938fa24c191f2af60f505480d`. A prova Lean 4.32 e a auditoria de 21 raízes estão registradas em `evidence/rational-boxes/degree1-weight-bound-validation.md` e nos logs associados. C5 continua parcial: os graus `2..14`, a cota analítica, as avaliações da fonte e a inclusão nas caixas seguem abertos.

## 1. Transporte algébrico Lean — PASSOU

Arquivos novos:

- `research/native-moving-schur-sigma/SigmaFiniteCoefficientSignTransport.lean`
- `research/native-moving-schur-sigma/SigmaFiniteCoefficientSignTransportAudit.lean`

A prova começa em `completedSigmaDisplacedSource_coefficient_recurrence` de C4 e mantém `completedSigmaDisplacedMoment = 2*completedSigmaLogJet`. O módulo prova a recorrência polinomial sem divisão, a identidade do menor escalado com `CarrySigmaPade.sigmaPadeD` original e os dois lemas de transferência de sinal usando `completedSigmaDisplacedSourceCoefficient_zero_pos`.

O build final foi feito para diretório de saída novo, com warnings tratados como erros, usando o script `compile_sigma_pade.sh`. Os logs e o comando exato estão em `build-transport-clean.log` e `transport-build-record.md`.

`#print axioms` para os quatro teoremas auditados lista apenas `propext`, `Classical.choice` e `Quot.sound`. Saída em `axiom-audit-transport-clean.log`. Nenhum axioma próprio, `sorryAx` ou `admit` foi introduzido.

PR #165 foi integrada à `main`; o GitHub não retornou status checks hospedados. A validação local registrada acima é o resultado de build/auditoria desta fase.

## 2. Genealogia da fonte — conferida, preservada

A revisão carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, em `CarrySelfAdjointOperator/C2GeometryNativeSourceBridge.lean`, prova
`canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar`:

```text
finiteBracketCharacteristic 2 cutoff s
  + ∑' index, centerBracketTerm 2 s (index + cutoff)
  = factor 2 s * nativeScalar s
```

O gerador numérico C5 avalia a mesma cabeça C2 mais cauda exata. Hurwitz é usado somente para avaliar a soma exata omitida; depois o fator nativo C2 e a completação original são aplicados. C4 liga os coeficientes resultantes aos jets originais. Hash da ponte carry e demais fontes em `pins-and-sha256.txt`.

## 3. Verificação racional condicional — PASSOU

O verificador `verify_signs_exact.py` usa `fractions.Fraction`; não usa Float para decidir sinal. Resultados nos JSONs rastreados:

| Deslocamento | Sinais condicionais | Log |
|---|---|---|
| `99/2000` | `+++++++++++-` | `interval-certificate/verify-d00495.log` |
| `1/10` | `+++++++++-` | `interval-certificate/verify-d01.log` |

Esses cálculos provam os sinais supondo as inclusões de todos os coeficientes nas caixas.

## 4. Geração intervalar — REPRODUZIDA, não é ainda prova formal

As três configurações pedidas passaram após uma correção apenas de compatibilidade de backend, registrada como patch:

1. `d=.0495`, `L=0`, `N=1024`, `r/R=.30/.40`; sinais `+++++++++++-`.
2. `d=.0495`, `L=12`, `N=512`, `r/R=.20/.40`; sinais `+++++++++++-`.
3. `d=.1`, `L=12`, `N=512`, `r/R=.15/.30`; sinais `+++++++++-`.

Cada saída foi conferida pelo verificador exato em um segundo passo. JSONs e logs de geração e verificação estão em `interval-certificate/`.

A primeira execução falhou antes de produzir JSON porque esta instalação do `mpmath 1.3.0` seleciona `gmpy2.mpz`, que `Decimal` não aceita. A falha foi preservada em `sign1024_stirling-initial-gmpy2-failure.log`. No checkout Momentos isolado foi testada uma conversão explícita `int(mpz)`; o patch correspondente está versionado ao lado. A branch remota da PR #2 não foi alterada.

O avaliador permanece experimental: as funções elementares `mpmath.iv` e sua garantia de arredondamento externo não foram provadas em Lean. Portanto, as caixas ainda não são inclusões formais dos coeficientes verdadeiros.

## 5. Sinais condicionais — provados em Lean

O3 compõe as caixas racionais com a recorrência polinomial sem divisão e prova
em Lean os sinais condicionais dos menores. Os teoremas
`sigmaPadeD_signs_at_99_2000_of_source_boxes` e
`sigmaPadeD_signs_at_1_10_of_source_boxes` concluem sobre o `sigmaPadeD`
original, assumindo respectivamente `sigmaC00495SourceBoxes` e
`sigmaC01SourceBoxes`. Todos os índices requeridos foram cobertos: `D₀..D₁₀>0,
D₁₁<0` em `d=99/2000` e `D₀..D₈>0, D₉<0` em `d=1/10`.

O build limpo dos seis módulos e a auditoria das 13 raízes passaram; apenas
`propext`, `Classical.choice` e `Quot.sound` aparecem. Consulte
`evidence/rational-boxes/VALIDATION.md` para comandos, logs e hashes.

## 6. Resultado incondicional — ainda aberto

Os dois teoremas finais de primeira janela negativa ainda não são
incondicionais, pois O4 não prova que os coeficientes reais da fonte C2 original
estão dentro das caixas. A fonte permanece a cabeça C2, a cauda exponencial
exata e a completação original; os resultados condicionais não substituem essa
prova. A primeira obrigação aberta está em `OPEN_OBLIGATIONS.md`.
