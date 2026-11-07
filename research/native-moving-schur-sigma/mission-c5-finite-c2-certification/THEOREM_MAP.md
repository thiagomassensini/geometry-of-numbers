# C5 — mapa dos teoremas e obrigações

## Recorrência nodal m=2 até n=16 (PR #271 integrada; C5 parcial)

`SigmaC5M2TaylorStateStage16Certificate.lean` prova
`c5RoundedExpStateC_stage16_correct` para `(a,j)=(2/5,0)`, importando o estado
`n=15`. A transição verifica o produto intervalar, `1/1307674368000`, os
arredondamentos e a soma. Lean 4.32.0 com `warningAsError=true` passou; a
auditoria mostra somente axiomas padrão. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage16-20261107/`.

A PR #271 integrou o commit `3e9f0e225e426e92a86430ec6d1a22b093ed04af` no merge `795caa0eebfaa61874c1fff22c683fb85bdf941a`; o GitHub não reportou
checks hospedados. Não fecha `n=192`, os demais nós, quadraturas, caixa
completa, inclusão dos coeficientes C2 originais ou sinais finais. Próximo
estado: `n=17`.

## Recorrência nodal m=2 até n=15 (PR #269 integrada)

`c5RoundedExpStateC_stage15_correct` foi integrado pelo commit `2dd2bb75153245bb13613135a66721f7a992fcea` e
merge `fe6d5c238ba9ee796dc5ef56880aa60e89899c63`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage15-20261107/`. Isso não
fecha a recorrência completa, as inclusões nem os sinais C5.

## Recorrência nodal m=2 até n=14 (PR #267 integrada)

`c5RoundedExpStateC_stage14_correct` foi integrado pelo commit `eaf5a2a71a5d896d4521e2b7cf969421343b3982` e
merge `b1a7c9b14eb1352cc470508fdb2bf9a8baaea56a`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage14-20261107/`. Isso não
fecha a recorrência completa, as inclusões nem os sinais C5.

## Recorrência nodal m=2 até n=13 (PR #265 integrada)

`c5RoundedExpStateC_stage13_correct` foi integrado pelo commit `4c4856c022eb302b013d36c10806d609770c42d2` e
merge `52c57108c74cb5f7f12bdbd94ca616f3bba8cf2a`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage13-20261107/`. Isso não
fecha a recorrência completa, as inclusões nem os sinais C5.

## Recorrência nodal m=2 até n=12 (PR #263 integrada)

`SigmaC5M2TaylorStateStage12Certificate.lean` prova
`c5RoundedExpStateC_stage12_correct` para `(a,j)=(2/5,0)`. A PR #263 integrou
o commit `b7c442c318de488cb928fc8e456110b4b27a81f4` no merge
`4b5b6a0aebd54798e6a26b2eda69994589c78668`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage12-20261107/`. Isso não
fecha a recorrência completa nem as inclusões/sinais C5.

## Recorrência nodal m=2 até n=10 (PR #259 integrada; C5 parcial)

`SigmaC5M2TaylorStateStage10Certificate.lean` prova
`c5RoundedExpStateC_stage10_correct` para `(a,j)=(2/5,0)`, importando o estado
`n=9`. A transição certifica o produto de intervalos não-positivos, o
coeficiente `1/362880`, o arredondamento e a soma. Lean 4.32.0 com
`warningAsError=true` passou; a auditoria usa somente axiomas padrão. Evidência
em `evidence/rational-boxes/c5-m2-dirichlet-term-stage10-20261107/`.

A PR #259 integrou o commit de prova
`5dd4f4874a192e83af26640f412f81f42239487b` no merge
`d68eec91118e2cdcb89fced66a14062ef6170cf9`; o GitHub não reportou checks
hospedados. Não fecha `n=192`, os outros nós, quadraturas, caixa completa,
inclusão dos coeficientes C2 originais nem os sinais finais. Próximo estado:
`n=11`.

## Recorrência nodal m=2 até n=9 (PR #257 integrada; C5 parcial)

`SigmaC5M2TaylorStateStage9Certificate.lean` prova
`c5RoundedExpStateC_stage9_correct` para `(a,j)=(2/5,0)`, importando o estado
`n=8`. A transição certifica o produto de sinais conhecidos, o coeficiente
`1/40320`, o arredondamento e a soma. Lean 4.32.0 com `warningAsError=true`
passou; a auditoria usa somente axiomas padrão. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage9-20261107/`.

A PR #257 integrou o commit de prova
`62c9fbd7b04034f21ccf0336abf0d83d8c6a6592` no merge
`9655308b17dbf565d272f7578545bb68b7b0b867`; o GitHub não reportou checks
hospedados. Não prova a recorrência até `n=192`, os demais nós, quadraturas,
caixa completa, inclusão dos coeficientes C2 originais nem os sinais finais.
Próximo estado: `n=10`.

## Recorrência nodal m=2 até n=8 (PR #255 integrada; C5 parcial)

`SigmaC5M2TaylorStateStage8Certificate.lean` prova
`c5RoundedExpStateC_stage8_correct` para `(a,j)=(2/5,0)`, importando o estado
`n=7`. A prova verifica o produto de intervalos não-positivos, o coeficiente
`1/5040`, o arredondamento e a soma. Lean 4.32.0 com `warningAsError=true`
passou; a auditoria mostra somente axiomas padrão. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage8-20261107/`.

A PR #255 integrou o commit de prova
`96f5f5709829282756bc8c8a2b52a80290c96735` no merge
`29d363068d52c62c37afc3896f6b3d46f734f16b`; o GitHub não reportou checks
hospedados. Não prova a série até `n=192`, os demais termos, quadraturas, caixa
nodal completa, inclusão dos coeficientes C2 originais nem os sinais finais.
Próximo estado: `n=9`.

## Recorrência nodal m=2 até n=7 (PR #253 integrada; C5 parcial)

`SigmaC5M2TaylorStateStage7Certificate.lean` prova
`c5RoundedExpStateC_stage7_correct` para `(a,j)=(2/5,0)`, importando o estado
`n=6`. A transição verifica o produto intervalar com sinais conhecidos, o
coeficiente `1/720`, o arredondamento e a atualização da soma. Lean 4.32.0
com `warningAsError=true` passou; a auditoria mostra apenas axiomas padrão.
Evidência em `evidence/rational-boxes/c5-m2-dirichlet-term-stage7-20261107/`.

A PR #253 integrou o commit de prova
`a08a5c9c5a1d02fc33b3207ef2be3d362d526de8` no merge
`952fcd76093681f3feacc540bb0db9c49bfc6034`; o GitHub não reportou checks
hospedados. Não prova a recorrência até `n=192`, os demais termos, quadraturas,
caixa nodal completa, inclusão dos coeficientes C2 originais nem os sinais
finais. Próximo estado: `n=8`.

## Recorrência nodal m=2 até n=6 (PR #251 integrada; C5 parcial)

`SigmaC5M2TaylorStateStage6Certificate.lean` prova
`c5RoundedExpStateC_stage6_correct` para `(a,j)=(2/5,0)`, importando o estado
`n=5`. O passo usa o coeficiente `1/120`, verifica o termo arredondado e
atualiza a soma por aritmética racional. Lean 4.32.0 com
`warningAsError=true` passou; a auditoria mostra apenas axiomas padrão.
Evidência em `evidence/rational-boxes/c5-m2-dirichlet-term-stage6-20261107/`.

A PR #251 integrou o commit de prova
`e6c9ef307c69c59a8e665232b4b0271c481d8fcd` no merge
`7b61a5ceb0d8567c33fe27a5810d493f4640ed69`; o GitHub não reportou checks
hospedados. Não prova a série até `n=192`, os demais termos, quadraturas, caixa
nodal completa, inclusão dos coeficientes C2 originais nem os sinais finais. O
próximo estado a certificar é `n=7`.

## Recorrência nodal m=2 até n=5 (PR #249 integrada; C5 parcial)

`SigmaC5M2TaylorStateStage5Certificate.lean` prova
`c5RoundedExpStateC_stage5_correct` para `(a,j)=(2/5,0)`, importando o estado
`n=4` integrado pela PR #247. O lema de produto de sinais mistos e a escala
`1/24` sustentam a atualização do quinto estado; floors e ceils são exatos.
A auditoria retorna apenas axiomas padrão. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage5-20261107/`.

Ainda não há prova do restante da série, das quadraturas, da caixa nodal ou da
inclusão dos coeficientes C2 originais. A PR #249 integrou este checkpoint, commit de prova `1782048f05c43fc31e491fa7192105235b34a14e`, merge
`58b9a61532f79f6aa51ebfb48edaacf728be3738`; o GitHub não reportou checks.


## Recorrência nodal m=2 até n=4 (PR #247 integrada; C5 parcial)

`SigmaC5M2TaylorStateStage4Certificate.lean` prova
`c5RoundedExpStateC_stage4_correct` para o nó `(2/5,0)`, importando o estado
`n=3` integrado pela PR #245. A prova usa a regra de intervalo
não-positivo×não-positivo e verifica a escala `1/6`, seus arredondamentos e a
atualização da soma. A auditoria exibe somente axiomas padrão. Evidências em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage4-20261107/`.

O teorema não cobre o restante da série, as quadraturas ou a caixa do nó
completo, e não liga a fonte C2 às caixas. A PR #247 integrou este checkpoint, commit de prova `7b355ce2349a242c133caf8d71b777c2a186c0a0`, merge
`ab6d5f1923770d4db830ba9ebf2fbc17c9626149`; o GitHub não reportou checks.


## Recorrência nodal m=2 até n=3 (PR #245 integrada; C5 parcial)

`SigmaC5M2TaylorStateStage3Certificate.lean` prova
`c5RoundedExpStateC_stage3_correct`, importando o estado `n=2` integrado pela
PR #243. O passo de produto usa intervalos com fator não-negativo e fator
não-positivo; a escala `1/2` e os dois coarsenings são certificados por
aritmética racional exata. A auditoria mostra apenas axiomas padrão. Evidências
estão em `evidence/rational-boxes/c5-m2-dirichlet-term-stage3-20261107/`.

O teorema cobre somente os estados Taylor até `n=3`, para um nó. Não cobre a
série completa, as quadraturas, a caixa nodal ou os coeficientes C2 originais.
A PR #245 integrou o checkpoint, commit de prova
`e264aea05ac6036dea612c5e9ca97c8c7cc81495`, merge
`727b3920d12e0979c5f722a04732fb346fc880d8`; o GitHub não reportou checks.


## Piloto nodal m=2 — Taylor até n=2 (PR #243 integrada; C5 parcial)

`SigmaC5M2TaylorStateStage2Refined.lean` prova
`c5RoundedExpStateC_stage2_correct_refined` para o argumento racional do nó
`(a,j)=(2/5,0)`. O estado parte do log `2` arredondado e do argumento após
quatro metades. Os lemas de produto real com sinal conhecido, coarsening exato
e atualização da soma eliminam as simplificações do produto complexo em uma
única tática. A prova compila e a auditoria retorna somente axiomas padrão.

Este teorema cobre `n=0,1,2`, não o Taylor completo com `n=192`, nem as quatro
quadraturas de `c5RoundedExpC`, nem a caixa `c5CenteredDirichletTermBox` inteira.
Ele ainda não demonstra a inclusão do coeficiente original na caixa racional.
A PR #243 integrou o checkpoint, commit de prova
`86d42067db230b661321190ca397bb496e855186`, merge
`20c30cec4b3964fc063d8eb3c93e09a41d319cfc`; não houve checks hospedados.
Fontes, exportação, erros e comando estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage2-20261107/README.md`.

## Recorrência genérica nos estágios 2–192 — provada e integrada pela PR #239

`SigmaC5ZeroExpGenericRecurrence.lean` prova
`c5RoundedExpC_zero_stage_2_to_192_closed_form`: para cada `2 ≤ k ≤ 192`, a
caixa da exponencial arredondada na entrada zero tem parâmetros
`3*2^(k-2)-1` e `4*2^(k-2)-1`. `c5GenericBox_square_coarsen` demonstra o passo
exato de arredondamento em 896 bits; os limites para `k≤192` justificam sua
aplicação em todo estágio. A auditoria isolada usa apenas axiomas padrão. O
PR #239 integrou a prova: commit `be04221f5eb4a174804fb96c9011d0b58bfc2642`,
merge na `main` `8c3691e59f9280864b93c4868eb465dbdad6da2c`; o GitHub não reportou
checks. Fontes, logs, pins, hashes e reprodução estão em
`evidence/rational-boxes/c5-generic-exp-recurrence-20261107/`.

Isto fecha a recorrência na entrada zero, mas ainda não liga as 516 caixas CSV
à avaliação nodal, não compõe Gamma/π/fonte C2 e não prova as inclusões O3.

## Exponencial arredondada no estágio 6 — provada e integrada pela PR #234

`SigmaC5ZeroExpStage6Certificate.lean` importa a igualdade integrada do
estágio 5, define `c5ZeroExpStage6Export` e prova `c5ZeroExpStage6_eq`. A caixa
real é `[(2^896 - 47)/2^896, (2^896 + 63)/2^896]`, e a parte imaginária é
`[-63/2^896, 63/2^896]`. Quatro lemas registram os extremos exatos do quadrado
e quatro provam os pisos/tetos. A auditoria das nove raízes mostra apenas
axiomas padrão. Build, auditoria, pins e hashes estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. Este subpasso ainda
foi integrado pela PR #234: commit de prova
`a9be0be89794465fefa44bf66c3b50d5702cc0f5`, merge na `main`
`5571ceb84e0483da55ff7ba212942a4ab13b7cab`; o GitHub não reportou checks.
Este subpasso não fecha a ponte CSV–Lean nem as inclusões C2.

## Exponencial arredondada no estágio 5 — provada e integrada pela PR #232

`SigmaC5ZeroExpStage5Certificate.lean` importa a igualdade integrada do
estágio 4, define `c5ZeroExpStage5Export` e prova `c5ZeroExpStage5_eq`. A caixa
real é `[(2^896 - 23)/2^896, (2^896 + 31)/2^896]`, e a parte imaginária é
`[-31/2^896, 31/2^896]`. Quatro lemas registram os extremos exatos do quadrado
e quatro provam os pisos/tetos. A auditoria das nove raízes mostra apenas
axiomas padrão. Build, auditoria, pins e hashes estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. Este subpasso ainda
foi integrado pela PR #232: commit de prova
`821b119d4f0d506e685a585d7f3a52c00a6a95d5`, merge na `main`
`75bacc9c2b7ca8113ee906c61a411922e01bb978`; o GitHub não reportou checks.
Este subpasso não fecha a ponte CSV–Lean nem as inclusões C2.

## Exponencial arredondada no estágio 4 — provada e integrada pela PR #230

`SigmaC5ZeroExpStage4Certificate.lean` importa a igualdade integrada do
estágio 3 e prova `c5ZeroExpStage4_eq`: a caixa arredondada na entrada zero é
exatamente `c5ZeroExpStage4Export`. Quatro lemas registram os extremos exatos
do quadrado e quatro provam os pisos/tetos. A auditoria das nove raízes mostra
apenas axiomas padrão. Build, auditoria, pins e hashes estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. O commit de prova
`fe2df2cd361d0d5096d6c4503468833e364b4481` foi integrado pela PR #230, merge
na `main` `f89cb99d6790bb2c84985c67022b8045a7fb181f`; o GitHub não reportou
checks. Este subpasso não fecha a ponte CSV–Lean nem as inclusões C2.

## Exponencial arredondada no estágio 3 — provada e integrada pela PR #228

`SigmaC5ZeroExpStage3Certificate.lean` importa a igualdade integrada do
estágio 2 e prova `c5ZeroExpStage3_eq`: a caixa arredondada na entrada zero é
exatamente `c5ZeroExpStage3Export`. Quatro lemas registram os extremos exatos
da caixa quadrada e quatro provam seus pisos/tetos. A auditoria das nove raízes
mostra apenas axiomas padrão. Build, auditoria, pins e hashes estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. O commit de prova
`682eae99f4b05abd70ee8068aada7bc2af3e0ebb` foi integrado pela PR #228, merge
na `main`
`0d312c654015bf10384969e64f352b0313e2dd39`; o GitHub não reportou checks.
Este subpasso não fecha a ponte CSV–Lean nem as inclusões dos coeficientes C2.

## Exponencial arredondada no estágio 2 — provada e integrada pela PR #226

`c5ZeroExpStage2_eq` prova que a caixa `c5RoundedExpC 192 896 2` na entrada
zero é exatamente `c5ZeroExpStage2Export`. Quatro lemas provam os pisos/tetos
do estágio 1 por desigualdades racionais exatas. A auditoria de onze raízes
reporta somente axiomas padrão. Build, auditoria, pins e hashes em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. PR #226, commit de
prova `ab0f2782369e7f0966fa6c769d23ca18ea9abb1f`, merge na `main`
`96579150be6700793970bf8cd84f91dd2cccb102`; o GitHub não reportou checks.
Este subpasso não liga o CSV às caixas Lean nem prova as inclusões C2.

## Exponencial arredondada no estágio 1 — provada e integrada pela PR #224

`SigmaC5ZeroExpStagesCertificate.lean` prova
`c5ZeroExpStage1_eq`: a caixa `c5RoundedExpC 192 896 1` na entrada zero é
exatamente `c5ZeroExpStage1Export`. Os quatro extremos são certificados por
igualdades de piso/teto com desigualdades racionais exatas. A auditoria de
`c5ZeroExpStage0_eq`, dos quatro lemas de arredondamento e de `c5ZeroExpStage1_eq`
reporta somente axiomas padrão. Build, auditoria, pins e hashes em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`. PR #224, commit de
prova `a908789fad182aa9a2d8eb85b2da641c11c4da62`, merge na `main`
`d667abfc42020e442c62ec1b49b82f5bcf1971ad`; o GitHub não reportou checks.

Este subpasso não estabelece as igualdades das
516 linhas CSV com as caixas Lean, não compõe a fonte C2 completa e não prova
`sigmaC00495SourceBoxes` ou `sigmaC01SourceBoxes`; O4/C5 continua aberta.

## O4 integrado pela PR #209 — cobertura adaptativa de zeta nos 129 nós

Arquivos integrados: `SigmaC5RationalNodeLogBounds.lean` e
`SigmaC5RationalNodeInstantiate.lean`. Commit de prova
`05dae531d4ec10c916c340f58255f35977a3abdd`; merge da PR #209
`386b654eabe4c942d6b0db46754120ab79b52fb5`.

| Declaração | Status, hipóteses e limite |
|---|---|
| `CarrySigmaObstruction.c5LogQAdaptiveAbsBound` | PROVADO: limites racionais uniformes de `logQ` para `1≤m≤100`, com 128 parcelas. |
| `CarrySigmaObstruction.c5AdaptiveLogScaleReducedRange` | PROVADO: a escala adaptativa mantém `m/2^k∈[1/2,1]` nesse intervalo. |
| `CarrySigmaObstruction.c5RationalZetaAdaptiveTermSide` | PROVADO: constrói as condições de log/exp para cada termo, usando `normBound≤4`. |
| `CarrySigmaObstruction.c5RationalZetaAdaptiveHeadBox_contains` e `...BasePowerBox_contains` | PROVADO: constroem as caixas da cabeça e da potência-base sem hipóteses auxiliares do chamador. |
| `CarrySigmaObstruction.c5RationalZetaAdaptiveNodeBox_contains_at` | PROVADO: para `j≤128`, `b=j/100000` e `a∈[2/5,3/5]`, inclui zeta numa caixa racional; conserva a cauda `<10^-250`. |
| `CarrySigmaObstruction.c5RationalZetaAdaptiveNodeConjugateBox_contains_at` | PROVADO: estende a inclusão aos argumentos de parte imaginária negativa por conjugação. |

Build limpo Lean 4.32 e auditoria fail-closed de 21 raízes passaram; só
`propext`, `Classical.choice` e `Quot.sound` aparecem. Pins, hashes e logs em
`evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`.
Isto ainda não fornece extremos achatados nem compõe Gamma, π ou a fonte C2;
as inclusões dos coeficientes nas caixas O3 e a conclusão C5 permanecem abertas.

## O4 integrado pela PR #207 — avaliador racional genérico de zeta (incompleto)

Arquivo integrado: `research/native-moving-schur-sigma/SigmaC5RationalNodeEval.lean`.
Commit de prova `fb8bb31ed1fcbb4d1d9c88aceea1dd83539935df`; merge na `main`
`27a61e6bebcce178b81b961f507400ed77b96d3b`.

| Declaração | Status, hipóteses e limite |
|---|---|
| `CarrySigmaObstruction.c5RatComplexToComplex_pow` | PROVADO: potências de pares racionais são preservadas pela conversão a `ℂ`. |
| `CarrySigmaObstruction.c5RatPochhammer_toComplex` | PROVADO: Pochhammer finito racional complexo coincide com o coeficiente de Euler–Maclaurin em `ℂ`. |
| `CarrySigmaObstruction.c5RatCorrectionTerm_toComplex` | PROVADO: cada correção de Bernoulli racional coincide com sua parcela complexa Euler–Maclaurin. |
| `CarrySigmaObstruction.c5RatCorrectionSum_toComplex` | PROVADO: a soma finita das correções coincide com a soma em `ℂ`. |
| `CarrySigmaObstruction.c5RatScale_toComplex` | PROVADO sob não anulação do denominador: a escala racional coincide com a escala analítica finita. |
| `CarrySigmaObstruction.c5_emZetaHighRHS_factor` | PROVADO: para argumentos racionais, separa a cabeça finita, `100⁻ˢ` vezes a correção racional e a cauda exata EM. |
| `CarrySigmaObstruction.c5ComplexIntervalRangeSum_contains` | PROVADO: soma finita de caixas contém a soma dos valores incluídos. |
| `CarrySigmaObstruction.c5RationalZetaHeadBox_contains` | PROVADO CONDICIONALMENTE às hipóteses explícitas `hside` do avaliador de potências de Dirichlet. |
| `CarrySigmaObstruction.c5RationalZetaBasePowerBox_contains` | PROVADO CONDICIONALMENTE à condição log/exp explícita para `m=100`. |
| `CarrySigmaObstruction.c5RationalZetaNodeBox_contains` | PROVADO CONDICIONALMENTE para `2/5≤a≤3/5`, `0≤b≤128/100000` e as condições anteriores; contém `riemannZeta(a+bi)` após inflar o erro da cauda `<10^-250`. Não há instanciações nodais concretas. |

O build limpo e o checker das dez raízes passaram em Lean 4.32; somente os
axiomas padrão aparecem. Fonte, logs, pins, hashes e limite exato estão em
`evidence/rational-boxes/c5-rational-node-evaluator-validation.md`. O módulo
não compõe Gamma nem o escalar nativo C2 e não prova inclusões em O3.

## Snapshot atual — Gamma de núcleo racional integrada pela PR #198

Arquivo integrado: `research/native-moving-schur-sigma/SigmaC5GammaRationalCore.lean`.

| Declaração | Status, hipóteses e limite |
|---|---|
| `SigmaC5Gamma.gammaFinite_eq_rationalCore` | PROVADO E INTEGRADO: para `a,b,T∈ℚ`, `a>0`, separa `gammaFinite N T (a+bi)` em `T^(a+bi)` e soma finita exata em `ℚ+iℚ`. |
| `SigmaC5Gamma.gammaFiniteRationalCoreInterval_contains` | PROVADO E INTEGRADO: a caixa exata contém o valor racional complexo da soma. |
| `SigmaC5Gamma.gammaFiniteInterval_contains` | PROVADO E INTEGRADO, sob condições explícitas do avaliador `dirichletTermBox2`: a caixa contém a Gamma finita. |
| `SigmaC5Gamma.gamma3072Interval_contains` | PROVADO E INTEGRADO, para `1495/20000≤a≤1` e as hipóteses do avaliador: a caixa inflada por `10^-259` contém `Complex.Gamma (a+bi)`. |

Build limpo e auditoria de seis raízes: somente axiomas padrão. A prova ainda
não avalia qualquer nó concreto e não inclui os coeficientes C2 em O3; portanto
é uma ponte analítica de O4, não um certificado final. Evidência em
`evidence/rational-boxes/c5-gamma-rational-core-validation.md`. PR #198,
commit de prova `a1646a1837603aee7d03384016ae514a7f7c820a`, merge
`36cba9d805bc3274538cdc93bd0a3702154edcb2`.

## Snapshot atual — cota da fonte validada localmente

`SigmaC5AnalyticBounds.lean` prova localmente
`CarrySigmaObstruction.displacedProductC_norm_le_10pow13_on_ball_39`:
para `|d|≤1/10`, o módulo da fonte deslocada original é no máximo `10^13`
em `|z|<39/100`. Build limpo Lean 4.32 e auditoria fail-closed de quatro raízes
passaram, apenas com `propext`, `Classical.choice` e `Quot.sound`. Para Cauchy,
a interpolação usa contorno de raio `38/100`, estritamente dentro dessa região;
a estimativa racional continua `<10^-501`. Prova, hashes e logs estão em
`evidence/rational-boxes/analytic-bounds-10pow13-validation.md`. O limite
`10^100` integrado pela PR #191 permanece como wrapper compatível.

O4 segue aberta somente quanto à certificação dos valores nos 129 nós e à
inclusão dos coeficientes C2 originais nas caixas O3. Os sinais finais seguem
condicionais a essas inclusões; C5 não está concluída.

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

As três configurações de geração foram novamente reproduzidas em cópia
temporária, com conversão explícita de `gmpy2.mpz` para `int`, e verificadas
por frações exatas. Esse replay confirma os mesmos sinais condicionais, mas
não aumenta o status formal da inclusão das caixas. Veja
`evidence/interval-certificate/reproduction-2026-11-06.md`.

## O4 — infraestrutura formal encontrada; inclusão da fonte ainda ABERTA

### Domínio analítico da fonte deslocada — PROVADO E INTEGRADO

Arquivo: `research/native-moving-schur-sigma/SigmaC5SourceAnalytic.lean`.

| Declaração | Status |
|---|---|
| `displacedProductC_shiftedFactors_mem_completedNativeHeightDomain` | PROVADO: se `|d|≤1/10` e `|z|<2/5`, ambos os fatores da fonte deslocada estão no domínio analítico de altura original. |
| `displacedProductC_analyticOnNhd_ball` | PROVADO: o produto deslocado original é analítico no disco aberto de raio `2/5`. |
| `displacedProductC_analyticOnNhd_ball_00495` | PROVADO para `d=99/2000`. |
| `displacedProductC_analyticOnNhd_ball_01` | PROVADO para `d=1/10`. |

Build limpo e auditoria de quatro declarações passaram em Lean 4.32, com
`warningAsError=true` e apenas axiomas padrão. A evidência está em
`evidence/rational-boxes/source-analytic-domain-validation.md`.
Integrado pela PR #189: commit de prova
`e0272bfc9099031cb127ea0db8874900d9e8eca1`, merge
`3513a3b3854b105419d4f2cef245efac7ce88ba0`.
**Limite desta ponte de domínio:** ela não fornece cota numérica para o módulo.
O majorante explícito foi provado depois, localmente, em
`SigmaC5AnalyticBounds.lean`; continuam pendentes as avaliações racionais nos
nós e as inclusões dos coeficientes originais nas caixas. Ver o snapshot atual
no início deste mapa e `evidence/rational-boxes/analytic-bounds-validation.md`.

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
- Na data deste registro, os limites de grau `2..14`, a cota analítica da fonte e a inclusão das caixas seguiam abertos. O snapshot atual dos pesos aparece no fim deste mapa.

As quatorze raízes foram compiladas em Lean 4.32 e auditadas. Os comandos e hashes estão em `evidence/rational-boxes/VALIDATION.md` e `evidence/rational-boxes/source-and-olean-sha256.txt`. A expansão direta que excedeu o limite do simplificador está registrada em `interpolation-weight-degree1-prototype.log`.

**Limite de grau um — PROVADO E INTEGRADO:** os três teoremas acima foram
integrados pela PR #185; commit de prova `90a208df98e74a7c5ab1fe83a9ef0fc90c3d3cb6`,
merge `c840ba35711ac8f938fa24c191f2af60f505480d`. O build limpo Lean 4.32 e a
auditoria fail-closed de 21 raízes aceitam somente `propext`, `Classical.choice`
e `Quot.sound`. Evidência em `evidence/rational-boxes/degree1-weight-bound-validation.md`.
Naquele merge, o resultado cobria somente grau um e não fechava O4. Os graus
`2..14` foram provados no checkpoint local mais recente descrito abaixo.
# Estado atual dos pesos de interpolação — 2026-11-06

Além do grau um já integrado, a branch atual provou que, para `2≤n≤14`,
`c5InterpolationWeightSum n < 10^145`. O argumento usa os limites
`c5LagrangeBasis_zeroIndex_coeff_abs_le_two_pow`,
`c5LagrangeBasis_nonzeroIndex_coeff_abs_le_weight` e
`c5InterpolationCoeffAbsSum_le_four_mul_two_pow`. Build limpo e auditoria de
23 raízes passaram; ver
`evidence/rational-boxes/degree2-14-weight-bound-validation.md`. A etapa foi
integrada pela PR #187, merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
Na data daquele checkpoint, a cota analítica da fonte e a inclusão nas caixas
seguiam pendentes. A cota foi provada depois; a inclusão permanece aberta.
