# C5 — estado da sessão

## Estado atual — prefixo Bernoulli de 64 entradas integrado (2026-11-08)

- A PR #300 foi integrada na `main`: commit de prova `509e773`, merge `90e2f571efb482993682a05ccc938ee9aef388e5`.
- `c5BernoulliPrimeTable_64_eq_data` prova as entradas 0–63. A reprodução recompila sonda, tabela, certificados 32/64 e auditoria; os 601 valores coincidem com os literais por comparação racional exata.
- `CLEAN_BUILD=PASS`, `DATA_TABLE_CHECK=PASS`, `AXIOM_AUDIT=PASS`; a raiz usa somente `propext`, `Classical.choice`, `Quot.sound`. O certificado 0–64 levou 14:09 e 4.8 GiB RSS.
- As outras 537 entradas ainda carecem de igualdade formal. Próximo: certificar o prefixo 0–95, depois continuar até 601 e retomar a ponte de zeta. C5 e as inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes` seguem abertas.
- Evidência, comandos, tentativas e hashes: `evidence/rational-boxes/c5-bernoulli-data-prefix64-20261108/README.md`.

## Estado atual — igualdade formal do primeiro bloco Bernoulli integrada (2026-11-08)

- A PR #298 foi integrada na `main`: commit de prova `1ed4a00`, merge `171c19681482312bf71bffdcd23b24a728edf04b`.
- `c5BernoulliPrimeTable_32_eq_data` certifica os primeiros 32 valores da tabela recursiva contra o bloco literal. A reprodução compara exatamente todos os 601 valores da sonda Lean com os literais; `CLEAN_BUILD=PASS`, `DATA_TABLE_CHECK=PASS`, `AXIOM_AUDIT=PASS`.
- A auditoria isolada usa somente `propext`, `Classical.choice` e `Quot.sound`. A igualdade formal dos outros 569 valores não está provada; nenhum extremo CSV de zeta está ligado por este resultado a uma caixa Lean.
- Próximo: provar prefixos cumulativos em blocos de 32, iniciando em 32–64; ao chegar a 601, retomar a ponte formal de uma caixa de zeta. C5 e as inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes` permanecem abertas.
- Fontes e reprodução: `SigmaC5BernoulliData*.lean` e `evidence/rational-boxes/c5-bernoulli-data-prefix32-20261108/`.

## Estado atual — nó complementar de Gamma em `d=1/10` integrado (2026-11-08)

- Missão C5 continua ativa; C1B/C2/C3/C4 já estão concluídas. Não reiniciar fases anteriores nem a migração geral para Lean 4.35.
- PR #296 prova `CarrySigmaObstruction.c5GammaComplexNodeDOneUpperComplexBox_contains`, que contém `Complex.Gamma (3/10 + (3/20) * Complex.I)`. Com a PR #294, os dois pontos complexos da malha `d=1/10` estão fechados. Também estão integrados os nós `901/4000 + 3i/20` e `1099/4000 + 3i/20` para `d=99/2000`.
- `SigmaC5GammaDOneUpperLogBounds.lean` prova `|Interval.logQ 384 8 240| ≤ 10`, refinando a cota anterior 18 para caber no avaliador de potência de raio 8. A caixa compõe `240^z`, 16 blocos × 64 parcelas e o resto `gamma_finite_1024_240_error ≤ 10⁻⁹⁹`.
- Seis módulos passaram em Lean 4.32.0 com `warningAsError=true`; 16 relatórios aceitam somente `propext`, `Classical.choice` e `Quot.sound`, sem `sorryAx`, axiomas próprios ou `native_decide`. Pico RSS: 8.4 GiB. A reprodução limpa passou.
- Commit de prova `e986390937265fc1bb759140ed7fb6d80d23eadf`; PR #296; merge na `main` `113ed1517fff040f4fc619cf7d5086c57f137427`. Evidência, primeira falha, pins, logs e hashes: `evidence/rational-boxes/c5-gamma-d1-upper-complex-node-20261108/README.md`.
- Próximo: formalizar a ligação por nó entre as 516 caixas de zeta exportadas e as caixas usadas na avaliação Lean. A exportação CSV/`#eval` cobre os 129 nós e quatro coordenadas, mas ainda não demonstra a igualdade da caixa; Euler–Maclaurin de ordem 600 já está provada e integrada. Depois faltam os demais nós, a composição com fator nativo/quadraturas e as inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. C5 continua incompleta.

## Histórico — caixa Gamma em `1/5` integrada pela PR #285

- `CarrySigmaObstruction.c5GammaCoreFirstNodeBox_contains` contém `Complex.Gamma (1/5 : ℂ)`, compondo a potência, núcleo racional em 16 blocos e erro `gamma_finite_1024_240_error`.
- PR #285 integrou o commit `742dd764df81ee75bd487d1bf21e5a9afa5519c5`; merge `832b201b6907c6682aa9657c3e4ff9da6dd40254`.
- Evidência: `evidence/rational-boxes/c5-gamma-first-node-20261107/README.md`.

## Histórico — checkpoint do núcleo Gamma racional por blocos (PR #282)

- Base de `main`: merge da PR #281, `ec5c5e8998b62726ada6f942cf4c2410048a2a23`; branch de trabalho `codex/c5-o4-after-stage19-20261107`. Geometry de referência está em `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry em `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Integração: PR #282, commit de prova `131d5f57da009a830c0a967bb5cf4713412c3473`, merge `7c301a2bb0b975369c8f8889ec2940372d2266c2` em 2026-11-07. O checkpoint já está na `main`.
- Para `gammaFiniteRationalCore 1024 240 (1/5) 0`, 16 blocos de 64 termos têm seus pisos certificados em Lean. A recomposição dá a caixa exata do núcleo racional `[S/2^1024,(S+16)/2^1024] × {0}`; a inclusão está em `c5GammaCoreNodePilotChunkBox_contains`. Auditoria isolada: 20 raízes, somente `propext`, `Classical.choice`, `Quot.sound`, sem `sorryAx` nem `native_decide`; Lean 4.32 com warnings como erros.
- Escopo: um ponto e só o núcleo racional. A caixa ainda não inclui `240^z`, `gammaFinite`, Gamma completa, zeta, os demais nós nem os coeficientes da fonte C2. `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes` seguem sem prova; C5 permanece incompleta.
- Fontes, comandos, logs de tentativas falhas, checker e hashes estão em `evidence/rational-boxes/c5-gamma-core-node-pilot-20261107/README.md`. Não repetir a prova monolítica nem usar o caminho `native_decide`.
- Próximo: compor esta caixa com a inclusão formal da potência e o erro `gamma_finite_1024_240_error`, fechar uma caixa Gamma para o ponto e só então expandir para os nós de interpolação.


## Snapshot anterior — estado após PR #280 (2026-11-07)

- A última integração de prova na `main` é a PR #280: commit `8a8fcde3682f804a2e3cdb03dae2be5d71d54654`, merge `de09a348a9e2b0f0c6bd700eeed63d92726a56c5`. Esta atualização de estado foi preparada na branch `codex/c5-stage19-state-20261107` sobre essa base.
- C1B já entrou pela PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`; C2 pela PR #157, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`; C3 pela PR #159, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`. C4 e a recorrência dos momentos também estão integradas. Não reabrir essas fases nem a migração geral para Lean 4.35.
- C5 O2 (`SigmaFiniteCoefficientSignTransport`) está provada em Lean 4.32: recorrência polinomial sem divisão e transporte do sinal para `sigmaPadeD` original. O3 também está provada e auditada, mas **condicionada** às inclusões `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
- Reproduzi as três configurações de `certify_finite_c2.py`; o verificador racional exato confirmou `+++++++++++-`, `+++++++++++-` e `+++++++++-`. Logs, JSONs e hashes: `evidence/rational-boxes/reproduction-20261107/`. A execução precisou do patch local `gmpy2.mpz`→`int`, já preservado em `evidence/interval-certificate/momentos-gmpy2-compat.patch`; o checkout Momentos foi restaurado limpo. Esses resultados continuam condicionais e não provam a inclusão formal da fonte.
- A PR #213 já exportou 516 caixas racionais de zeta nos 129 nós e quatro coordenadas. `#eval`/CSV confirma a exportação e a cobertura, mas ainda não há prova Lean de que cada valor exportado seja igual à caixa usada na composição. A tentativa monolítica para uma caixa está documentada como falha; não a repetir.
- Último resultado formal para a recorrência nodal: `c5RoundedExpStateC_stage18_correct` já está integrado pela PR #275; `c5RoundedExpStateC_stage19_correct` também compilou e passou pela auditoria Lean 4.32, integrado pela PR #280 (commit `8a8fcde3682f804a2e3cdb03dae2be5d71d54654`). Evidência completa em `evidence/rational-boxes/c5-m2-dirichlet-term-stage19-20261107/`.
- A PR #279 integrou `c5CenteredDirichletTermBox_one_eq_generic` e `c5CenteredDirichletTermBox_one_fixed` (commit `aa542db5f40bc8d1cb5cf76c3ef8d46358702cb0`, merge `b06200968bc004694ee8d7acc3af88463d40ebf2`). O primeiro termo da cabeça, `m=1`, é exatamente `c5GenericBox 11 15`; build Lean 4.32 e auditoria padrão passaram. Isso não cobre os outros 98 termos nem a inclusão da fonte. Evidência em `evidence/rational-boxes/c5-centered-first-term-20261107/`.
- **Próxima obrigação:** fechar uma caixa Gamma completa no primeiro ponto usando a caixa certificada do núcleo racional, a inclusão formal de `240^z` e `gamma_finite_1024_240_error`; depois estender a composição aos nós da interpolação e provar `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. Não repetir a prova monolítica nem ampliar Taylor sem dependência concreta.
- Alvo final: provar incondicionalmente os sinais de `sigmaPadeD` original em `d=99/2000` e `d=1/10`. A missão permanece incompleta até as inclusões da fonte e a composição final passarem build e auditoria.


## Checkpoint — recorrência nodal `m=2`, `n=18→19` (PR #280 integrada)

`SigmaC5M2TaylorStateStage19Certificate.lean` prova
`c5RoundedExpStateC_stage19_correct` para `(a,j)=(2/5,0)`, usando o estado
`n=18` da PR #275. Lean 4.32.0 compilou com `warningAsError=true`; as cinco
raízes auditadas dependem somente de `propext`, `Classical.choice` e
`Quot.sound`, sem `sorryAx`. O probe exportou seis limites racionais; o estado
`n=19` tem potência negativa, termo de Taylor positivo e soma acumulada positiva.
Builds, falha inicial preservada, pins, comandos e hashes estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage19-20261107/`. A compilação
observou 60.45 GiB de `MemAvailable` sob o limite de 30 GiB.

O alcance é apenas uma transição em um nó. Não prova a caixa C2 completa, as
inclusões da fonte nem os sinais finais. A PR #280 integrou o commit de prova `8a8fcde3682f804a2e3cdb03dae2be5d71d54654` na `main` pelo merge
`de09a348a9e2b0f0c6bd700eeed63d92726a56c5`. O GitHub não reportou checks
hospedados. Este checkpoint segue parcial.

## Checkpoint auxiliar — estágio Taylor 18 do nó m=2 integrado pela PR #275

Na branch de prova `codex/c5-m2-stage18-20261107`, baseada na `main` em
`0807c1052a9e5ac4464139e1593958a495a80103`, foi provada
`c5RoundedExpStateC_stage18_correct` para `(a,j)=(2/5,0)`. Lean 4.32.0 com
`warningAsError=true` terminou em `BUILD_EXIT=0`; as cinco declarações
auditadas dependem somente de axiomas padrão, sem `sorryAx`. Fontes, pins,
logs e hashes estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage18-20261107/`.
O commit `eb7209321914de6733de0bd160e1c64633924dba` foi integrado pela PR #275 no merge `df23788957cb17b16832d5f4c9e47fd8aa12d68f`; o GitHub não
reportou checks hospedados.

O resultado cobre somente `n≤18` de um nó. Os estados restantes, demais nós,
quadraturas, caixa completa, inclusão da fonte C2 e sinais finais seguem
abertos. C5 permanece incompleta. Após o lema integrado do termo `m=1`, a transição `n=18→19` do termo `m=2` foi compilada, auditada e integrada pela PR #280.

## Checkpoint anterior — estágio Taylor 17 integrado pela PR #273

`c5RoundedExpStateC_stage17_correct` entrou na `main` pelo commit `0783b090aa4f9b6faf7ecd3605c187ae46352498`
e merge `41164de6cf0042594833bae02cdab2ce4cd11aae`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage17-20261107/`.

## Checkpoint anterior — estágio Taylor 16 integrado pela PR #271

`c5RoundedExpStateC_stage16_correct` entrou na `main` pelo commit `3e9f0e225e426e92a86430ec6d1a22b093ed04af`
e merge `795caa0eebfaa61874c1fff22c683fb85bdf941a`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage16-20261107/`.

## Checkpoint anterior — estágio Taylor 15 integrado pela PR #269

`c5RoundedExpStateC_stage15_correct` entrou na `main` pelo commit `2dd2bb75153245bb13613135a66721f7a992fcea`
e merge `fe6d5c238ba9ee796dc5ef56880aa60e89899c63`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage15-20261107/`.

## Checkpoint anterior — estágio Taylor 14 integrado pela PR #267

`c5RoundedExpStateC_stage14_correct` entrou na `main` pelo commit
`eaf5a2a71a5d896d4521e2b7cf969421343b3982` e merge `b1a7c9b14eb1352cc470508fdb2bf9a8baaea56a`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage14-20261107/`.

## Checkpoint anterior — estágio Taylor 13 integrado pela PR #265

`c5RoundedExpStateC_stage13_correct` entrou na `main` pelo commit `4c4856c022eb302b013d36c10806d609770c42d2`
e merge `52c57108c74cb5f7f12bdbd94ca616f3bba8cf2a`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage13-20261107/`.

## Checkpoint anterior — estágio Taylor 12 integrado pela PR #263

`c5RoundedExpStateC_stage12_correct` foi integrado pelo commit de prova
`b7c442c318de488cb928fc8e456110b4b27a81f4`, merge
`4b5b6a0aebd54798e6a26b2eda69994589c78668`. A evidência correspondente fica
em `evidence/rational-boxes/c5-m2-dirichlet-term-stage12-20261107/`.

## Atualização — estágio Taylor 10 do nó m=2 integrado pela PR #259

Na branch local `codex/c5-m2-stage10-20261107`, baseada na `main` após PR #258
(`72d91196e14289f1818e33b539776f6fa80f8413`), foi provada
`c5RoundedExpStateC_stage10_correct` para `(a,j)=(2/5,0)`. Lean 4.32.0 com
`warningAsError=true` compilou em `BUILD_EXIT=0`, usando os pins Geometry e
Carry indicados na evidência. As cinco declarações auditadas usam somente
axiomas padrão, sem `sorryAx`. Fonte, probe, logs e hashes estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage10-20261107/`.
O commit de prova `5dd4f4874a192e83af26640f412f81f42239487b` foi integrado pela
PR #259 no merge `d68eec91118e2cdcb89fced66a14062ef6170cf9`; o GitHub não
reportou checks hospedados.

O checkpoint cobre somente `n≤10` para um nó. Os estados seguintes, demais
nós, quadraturas, caixa completa, inclusão da fonte C2 e sinais finais
continuam abertos. C5 permanece incompleta. Próximo: continuar com `n=11`.

## Atualização — estágio Taylor 9 do nó m=2 integrado pela PR #257

Na branch local `codex/c5-m2-stage9-20261107`, baseada na `main` após PR #256
(`27c5496a55dd3bbf2fbca5b7fe92371f7ab44662`), foi provada
`c5RoundedExpStateC_stage9_correct` para `(a,j)=(2/5,0)`. Lean 4.32.0 com
`warningAsError=true` terminou em `BUILD_EXIT=0`; Geometry e Carry foram
compilados nos pins registrados na evidência. As cinco declarações auditadas
usam somente axiomas padrão, sem `sorryAx`. Fonte, probe, logs e hashes estão
em `evidence/rational-boxes/c5-m2-dirichlet-term-stage9-20261107/`.

O commit de prova `62c9fbd7b04034f21ccf0336abf0d83d8c6a6592` foi integrado
pela PR #257 no merge `9655308b17dbf565d272f7578545bb68b7b0b867`; o GitHub não
reportou checks hospedados.

O checkpoint cobre somente `n≤9` de um nó. Os estados restantes, outros nós,
quadraturas, caixa completa, inclusão da fonte C2 e sinais finais continuam
abertos. C5 permanece incompleta. Próximo: seguir para `n=10`.

## Atualização — estágio Taylor 8 do nó m=2 integrado pela PR #255

Na branch local `codex/c5-m2-stage8-20261107`, baseada na `main` após PR #254
(`e6a05bb60a866502400d163923d5ae749db48d9c`), foi provada
`c5RoundedExpStateC_stage8_correct` para `(a,j)=(2/5,0)`. Lean 4.32.0 com
`warningAsError=true` terminou em `BUILD_EXIT=0`; Geometry está pinado em
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry em
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. As cinco declarações auditadas
dependem somente de axiomas padrão, sem `sorryAx`. A fonte, o probe, os logs,
pins e hashes estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage8-20261107/`.
O commit de prova `96f5f5709829282756bc8c8a2b52a80290c96735` foi integrado pela
PR #255 no merge `29d363068d52c62c37afc3896f6b3d46f734f16b`; o GitHub não
reportou checks hospedados.

O checkpoint cobre somente a recorrência até `n=8` de um nó. Não fecha os
estados restantes, quadraturas, caixa completa, inclusões da fonte C2 ou sinais
finais. C5 permanece incompleta. Próximo: continuar com `n=9`.

## Atualização — estágio Taylor 7 do nó m=2 integrado pela PR #253

Na branch local `codex/c5-m2-stage7-20261107`, baseada na `main` após PR #252
(`c0d2b4799ce81a5428ee84b68a886bd656441779`), foi provada
`c5RoundedExpStateC_stage7_correct` para `(a,j)=(2/5,0)`. O build Lean 4.32.0
com `warningAsError=true` terminou com `BUILD_EXIT=0`; Geometry está pinado em
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry em
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. As cinco declarações auditadas
têm somente axiomas padrão, sem `sorryAx`. A fonte, o probe de exportação, os
logs, pins e hashes estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage7-20261107/`.
O commit de prova `a08a5c9c5a1d02fc33b3207ef2be3d362d526de8` foi integrado pela
PR #253 no merge `952fcd76093681f3feacc540bb0db9c49bfc6034`; o GitHub não
reportou checks hospedados.

Este checkpoint cobre somente a recorrência até `n=7` de um nó. Não fecha os
estados restantes, quadraturas, caixa completa, inclusões da fonte C2 ou sinais
finais. C5 permanece incompleta. Próximo passo: avançar para `n=8`.

## Atualização — estágio Taylor 6 do nó m=2 integrado pela PR #251

Na branch local `codex/c5-m2-stage6-20261107`, baseada na `main` após PR #250
(`850582ec76a9819149df2cbad4eba49f3e666e40`), foi provada
`c5RoundedExpStateC_stage6_correct` para `(a,j)=(2/5,0)`. A compilação final
usou Lean 4.32.0, `warningAsError=true`, Geometry no pin
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry no pin
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`; terminou com `BUILD_EXIT=0`.
As cinco declarações auditadas têm somente axiomas padrão, sem `sorryAx`.
Fonte, logs, pins, checksums e reprodução estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage6-20261107/`.
O commit de prova `e6c9ef307c69c59a8e665232b4b0271c481d8fcd` foi integrado pela
PR #251 no merge `7b61a5ceb0d8567c33fe27a5810d493f4640ed69`; o GitHub não
reportou checks hospedados.

O resultado cobre somente a recorrência Taylor até `n=6` em um nó. Não cobre
`n=7…192`, os demais nós, as quadraturas, o nó completo, a ponte CSV–Lean, as
inclusões dos coeficientes da fonte C2 ou os sinais finais. C5 continua
incompleta. Próximo passo nesta trilha é continuar com `n=7`.

## Atualização — nó m=2 validado até n=5 (PR #249 integrada)

Na branch `codex/c5-m2-stage5-20261107`, baseada na `main` após PR #248
(`442b4904c41d47a63825040a3e42c3fef75763d4`), foi provado
`c5RoundedExpStateC_stage5_correct` para `(a,j)=(2/5,0)`. A prova certifica o
produto com sinais mistos, o coeficiente `1/4! = 1/24`, o arredondamento e a
soma. Lean 4.32.0, `warningAsError=true`; as cinco raízes auditadas têm
somente axiomas padrão. Fonte, log, pin, hashes e comando estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage5-20261107/README.md`.
A PR #249 integrou o checkpoint, commit de prova `1782048f05c43fc31e491fa7192105235b34a14e`, merge na `main`
`58b9a61532f79f6aa51ebfb48edaacf728be3738`; o GitHub não reportou checks.

A prova cobre somente a recorrência até `n=5` de um nó. O próximo passo é
`n=6`; continuam abertos os outros termos, as quadraturas, a caixa completa,
a ponte CSV–Lean, as inclusões C2 e os sinais finais. C5 permanece incompleta.


## Atualização — transição do nó m=2 de n=3 para n=4 integrada pela PR #247 (2026-11-07)

Na branch `codex/c5-m2-stage4-20261107`, baseada na main após PR #246
(`61ffbda123b474184a6756deee9bbf57b2daa41c`), foi provado
`c5RoundedExpStateC_stage4_correct` para `(a,j)=(2/5,0)`. A prova reutiliza a
multiplicação de intervalos não-positivos e certifica a escala `1/3! = 1/6`,
a soma e os coarsenings em 896 bits. Lean 4.32.0 com
`warningAsError=true` passou; as cinco declarações auditadas têm somente
axiomas padrão. Fonte, log, pin, hash e reprodução estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage4-20261107/README.md`.
A PR #247 integrou o checkpoint, commit de prova `7b355ce2349a242c133caf8d71b777c2a186c0a0`, merge na `main`
`ab6d5f1923770d4db830ba9ebf2fbc17c9626149`; o GitHub não reportou checks.

O escopo continua restrito à recorrência até `n=4` de um único nó. Ainda não
há avaliação formal dos 192 termos, das quadraturas, da caixa nodal completa,
da ponte CSV–Lean ou das inclusões da fonte C2. O próximo passo é `n=5`.
C5 permanece incompleta.


## Atualização — transição do nó m=2 de n=2 para n=3 integrada pela PR #245 (2026-11-07)

Na branch `codex/c5-m2-stage3-20261107`, baseada na main após PR #244
(`418d440c6b7c1feff274ae17156595d186942d0e`), foi provada a igualdade
`c5RoundedExpStateC_stage3_correct` para `(a,j)=(2/5,0)`. A prova separa o
produto intervalar de sinais mistos, a escala `1/2` do termo e os dois
arredondamentos em 896 bits. Lean 4.32.0 com `warningAsError=true` passou; as
cinco declarações auditadas têm somente axiomas padrão. Evidência, pin, hashes,
log e erro intermediário estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage3-20261107/README.md`.
A PR #245 integrou o checkpoint, commit de prova `e264aea05ac6036dea612c5e9ca97c8c7cc81495`, merge na `main`
`727b3920d12e0979c5f722a04732fb346fc880d8`; o GitHub não reportou checks.

O escopo é só a recorrência até `n=3`. Não fecha os 192 termos, as quadraturas,
a caixa completa do nó ou as inclusões da fonte C2. A próxima etapa é
`n=4`, seguindo o mesmo isolamento de multiplicação, escala e arredondamento.
C5 permanece incompleta.


## Atualização — piloto C5 do nó m=2, recorrência Taylor até n=2 (2026-11-07)

No branch local `codex/c5-m2-stage-transition-20261107`, baseado na `main`
`e96caa7b1850a0d2775c5f801ccfe598e4a2ee0d` (PR #242), foi compilada e auditada
uma prova para o nó `(a,j)=(2/5,0)`. O log `log 2` exportado e arredondado, o
argumento após quatro metades e os estados de Taylor `n=0,1,2` são tratados em
módulos Lean separados. O teorema novo é
`c5RoundedExpStateC_stage2_correct_refined`.

O build Lean 4.32.0 com `warningAsError=true` passou; as quatro declarações
auditadas têm apenas `propext`, `Classical.choice` e `Quot.sound`. Não há
`sorryAx` no build aceito. Evidências, hashes, fontes, o vetor exato exportado,
os logs de falha e o comando de retomada estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage2-20261107/README.md`.
O checkpoint foi publicado pela PR #243, commit de prova `86d42067db230b661321190ca397bb496e855186`, integrada na `main` pelo merge `20c30cec4b3964fc063d8eb3c93e09a41d319cfc`. O GitHub não reportou checks hospedados.

Escopo: a prova fecha somente o estado Taylor `n=2`. Não fecha os 192 termos,
a quadratura final do avaliador, a caixa completa do nó `m=2`, a ponte das 516
caixas CSV, as inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes` ou os
sinais finais C5. A tentativa monolítica anterior falhou ao reduzir em bloco
os quatro cantos do produto complexo; ela e a recuperação inválida `sorryAx`
estão preservadas como tentativas, não como validação. Próximo passo local:
certificar `n=3` com uma regra para sinais mistos e avaliar o custo de continuar
por estágios.


## Atualização — recorrência genérica provada e integrada pela PR #239 (2026-11-07)

`SigmaC5ZeroExpGenericRecurrence.lean` prova uma fórmula fechada para
`c5RoundedExpC 192 896 k (ComplexInterval.exact 0 0)` em todo `2 ≤ k ≤ 192`.
Com `r = k - 2`, o resultado é a caixa com parâmetros `3*2^r-1` e
`4*2^r-1`. O resto de Taylor permanece o da definição original. Build com
Lean 4.32.0 e `warningAsError=true`, além da auditoria separada, passaram com
somente axiomas padrão. O commit de prova `be04221f5eb4a174804fb96c9011d0b58bfc2642`
foi integrado pela PR #239 no merge da `main`
`8c3691e59f9280864b93c4868eb465dbdad6da2c`; o GitHub não reportou checks
hospedados. Logs, pins, hashes, erros de cache recuperados e comandos estão em
`evidence/rational-boxes/c5-generic-exp-recurrence-20261107/`.

C5 ainda não está concluída: a ponte CSV–Lean, as inclusões dos coeficientes
da fonte C2 e os sinais finais seguem abertos. A próxima obrigação matemática
é a ponte CSV–Lean e sua composição na fonte original.

## Atualização — replay das caixas intervalares repetido (2026-11-07)

As três configurações da fonte C2 foram executadas outra vez a partir do
checkout Momentos `68c9b5f0a196289e28a8e5586146707d27df6b75`. Sem patch, a
configuração de 1024 nós reproduziu o erro ambiental de conversão
`gmpy2.mpz` → `Decimal`, e o traceback foi arquivado. Aplicando o patch somente
a uma cópia temporária do script, as três gerações terminaram e passaram pelo
verificador de frações racionais. Os sinais condicionais foram
`+++++++++++-`, `+++++++++++-` e `+++++++++-`, idênticos aos registros
anteriores. Os novos logs, JSONs, saídas exatas, patch, hashes e comandos estão
em `evidence/interval-certificate/reproduction-2026-11-07.md`.

Este checkpoint foi publicado pela PR #237 e integrado na `main` no merge
`5fe7837e0f9509950aeb95777bdd220d68835ad8`; o GitHub não reportou checks
hospedados. A branch de prova partiu de `9fafe0d7db30e8a8391be863fe8d56dd3ca7ebfb`.

Esse replay é evidência numérica experimental: não formaliza a implementação
intervalar externa e não prova que os coeficientes originais pertençam às
caixas. A recorrência genérica de `2 ≤ k ≤ 192` foi formalizada, auditada e
integrada pela PR #239. C5/O4 permanece aberta. O trabalho continua pela ponte
CSV–Lean e pela composição da fonte C2.

## Estado da missão de negatividade (atualizado em 2026-11-07)

- C1B foi integrada pela PR #155, no merge `0586e238441096ecd2248e3f14bdac3a832af427`.
- C2 foi integrada pela PR #157, no merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`.
- C3 foi integrada pela PR #159, no merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`.
- A prioridade ativa continua sendo a certificação finita C5. Esses merges não
  dependem de uma migração geral para Lean 4.35; C2/C3 foram validadas em Lean 4.32.
- A lei distância × profundidade e os novos cadernos estão adiados até depois
  de C2/C3; não é preciso calcular a primeira profundidade de falha para a
  negatividade eventual já provada.

## Atualização mais recente — igualdade do estágio 6 integrada pela PR #234

`SigmaC5ZeroExpStage6Certificate.lean` importa a prova integrada do estágio 5,
define a caixa arredondada seguinte e prova que
`c5RoundedExpC 192 896 6` na entrada zero coincide com ela. Os extremos
racionais do quadrado do estágio 5 produzem os pisos/tetos `2^896 - 47`,
`2^896 + 63`, `-63` e `63`. Build Lean 4.32 (`warningAsError=true`) e auditoria
das nove raízes passaram, somente com axiomas padrão. Pins, hashes e logs estão
em `evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.

O commit de prova `a9be0be89794465fefa44bf66c3b50d5702cc0f5` foi integrado pela
PR #234, merge na `main`
`5571ceb84e0483da55ff7ba212942a4ab13b7cab`; o GitHub não reportou checks
hospedados. C5 continua incompleta: a ponte CSV–Lean, as inclusões dos
coeficientes da fonte C2 nas caixas e os sinais finais seguem abertos.

## Atualização anterior — igualdade do estágio 5 integrada pela PR #232

`SigmaC5ZeroExpStage5Certificate.lean` importa a prova integrada do estágio 4,
define a caixa arredondada seguinte e prova que
`c5RoundedExpC 192 896 5` na entrada zero coincide com ela. Os extremos
racionais do quadrado do estágio 4 e os pisos/tetos `2^896 - 23`,
`2^896 + 31`, `-31` e `31` foram certificados. Build Lean 4.32
(`warningAsError=true`) e auditoria das nove raízes passaram, somente com
axiomas padrão. Pins, hashes e logs estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.

O commit de prova `821b119d4f0d506e685a585d7f3a52c00a6a95d5` foi integrado pela
PR #232, merge na `main`
`75bacc9c2b7ca8113ee906c61a411922e01bb978`; o GitHub não reportou checks
hospedados. C5 continua incompleta: a ponte CSV–Lean, as inclusões dos
coeficientes da fonte C2 nas caixas e os sinais finais seguem abertos.

## Atualização anterior — igualdade do estágio 4 integrada pela PR #230

`SigmaC5ZeroExpStage4Certificate.lean` importa a prova integrada do estágio 3
e prova que `c5RoundedExpC 192 896 4` na entrada zero coincide com
`c5ZeroExpStage4Export`. Os extremos racionais do quadrado do estágio 3 e seus
pisos/tetos foram provados, resultando em `2^896 - 11`, `2^896 + 15`, `-15` e
`15`. Build Lean 4.32 (`warningAsError=true`) e auditoria das nove raízes
passaram; somente axiomas padrão aparecem. Pins, hashes, logs, comandos e o
erro inicial de caminho de import estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.

O commit de prova `fe2df2cd361d0d5096d6c4503468833e364b4481` foi integrado pela
PR #230, merge na `main`
`f89cb99d6790bb2c84985c67022b8045a7fb181f`; o GitHub não reportou checks
hospedados. C5 continua incompleta: a ponte CSV–Lean, as inclusões dos
coeficientes da fonte C2 nas caixas e os sinais finais seguem abertos.

## Atualização anterior — igualdade do estágio 3 integrada pela PR #228

`SigmaC5ZeroExpStage3Certificate.lean` importa a prova integrada do estágio 2
e prova que a caixa `c5RoundedExpC 192 896 3` na entrada zero coincide com
`c5ZeroExpStage3Export`. Quatro lemas registram os extremos exatos da caixa
quadrada e quatro certificam os pisos/tetos. Build Lean 4.32 (`warningAsError`
ativo) e auditoria das nove raízes passaram; somente axiomas padrão aparecem.
Evidências, pins, hashes e tentativas de desenvolvimento estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.

O commit de prova `682eae99f4b05abd70ee8068aada7bc2af3e0ebb` foi integrado pela
PR #228, merge na `main`
`0d312c654015bf10384969e64f352b0313e2dd39`; o GitHub não reportou checks
hospedados. C5 continua incompleta: ainda faltam a ponte CSV–Lean e as
inclusões dos coeficientes da fonte C2 nas caixas.

## Atualização anterior — igualdade do estágio 2 (PR #226)

A PR #226 integrou este checkpoint: commit de prova
`ab0f2782369e7f0966fa6c769d23ca18ea9abb1f`, merge na `main`
`96579150be6700793970bf8cd84f91dd2cccb102`. O GitHub não reportou checks
hospedados.

`c5ZeroExpStage2_eq` prova que `c5RoundedExpC 192 896 2` na entrada zero
coincide exatamente com `c5ZeroExpStage2Export`. Quatro lemas adicionais
provam os pisos/tetos da caixa quadrada do estágio 1 por desigualdades
racionais exatas. Build Lean 4.32 (`warningAsError=true`) e auditoria de onze
declarações passaram; somente axiomas padrão aparecem. Os logs, pins e hashes
estão em `evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.
O estágio 3 foi integrado pela PR #228; a igualdade exportada do estágio 4
está registrada na atualização mais recente.

C5 permanece incompleta: as caixas dos estágios 1 e 2 não ligam o CSV às caixas
Lean nem provam `sigmaC00495SourceBoxes` ou `sigmaC01SourceBoxes`.

## Atualização anterior — igualdade do estágio 1 (PR #224)

O checkpoint foi integrado pela PR #224, commit de prova
`a908789fad182aa9a2d8eb85b2da641c11c4da62`, merge na `main`
`d667abfc42020e442c62ec1b49b82f5bcf1971ad`. O GitHub não reportou checks
hospedados.

`SigmaC5ZeroExpStagesCertificate.lean` prova que a exponencial arredondada no
estágio 1, com argumento zero, coincide exatamente com os extremos racionais
exportados. Quatro lemas provam os pisos e tetos por desigualdades racionais
exatas. O build Lean 4.32 com `warningAsError=true` passou para os mesmos corpos
de prova; a auditoria por import foi compilada separadamente e retorna apenas
`propext`, `Classical.choice` e `Quot.sound` para as seis raízes. Fontes, logs,
hashes, pins e comandos estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.

Esse resultado fecha somente a igualdade do estágio 1. Não conecta o CSV às
caixas Lean, não avalia os outros termos da fonte original e não prova
`sigmaC00495SourceBoxes` nem `sigmaC01SourceBoxes`; C5 segue aberta. A
primeira recompilação redundante, com auditorias auxiliares embutidas, foi
interrompida após 3 minutos; uma segunda tentativa completa do mesmo corpo de
prova foi interrompida após 5 minutos de redução racional, sem erro matemático.
O build prévio dos mesmos corpos de teoremas e o módulo de auditoria por import
passaram.

## Contexto anterior — núcleo do nó `m = 1` (2026-11-07)

Foram acrescentadas provas exatas para o log centrado e o termo de Dirichlet
em `m = 1`, e para a recorrência da exponencial complexa no argumento zero.
O resto de Taylor continua incluído como inflação racional explícita. Os três
módulos alterados compilaram em Lean 4.32.0 com `warningAsError=true`; as
auditorias dos sete teoremas registraram somente axiomas padrão.

Naquele checkpoint a igualdade da caixa do estágio 1 seguia aberta; essa
lacuna foi fechada pela PR #224. A PR #222, commit de
prova `67e6cf9fdf86ac735b6ade80d2f4a64982968363`, continua sendo o merge que
integrou o núcleo inicial do nó trivial na `main` (`e55858690e296d00c88692b8f30902987e853137`).
O estado atual da prova de estágio 1 e sua publicação estão registrados na
seção mais recente e no `README.md` de evidências.

## Checkpoint mais recente — componente `log 2` certificado por blocos

`SigmaC5Log2Certified.lean` prova as somas `Interval.logSum 512 (±1/3)` em
16 blocos racionais de 32 termos, recompõe cada soma finita e prova a igualdade
exata `c5CenteredLog2I 512 = c5ExportedLogTwo512`. A compilação limpa em Lean
4.32.0 passou com warnings como erros; a auditoria fail-closed passou para as
três raízes e encontrou somente `propext`, `Classical.choice` e `Quot.sound`.
Não há `sorry` nem `sorryAx` na fonte ou no relatório.
O commit de prova `bd84a673b3c5c1c82168a6655c59ad6a28bbf127` foi integrado
pela PR #219, merge na `main` `d6ed8ad249ef69c33920164fe43821cc83f138a8`; o
GitHub não reportou checks hospedados.

Este resultado certifica somente o componente central `log 2`. Ele ainda não
liga as 516 linhas do CSV às caixas Lean, não avalia a cabeça/correções restantes
e não prova `sigmaC00495SourceBoxes` nem `sigmaC01SourceBoxes`; C5 permanece
incompleta. O primeiro erro aberto continua sendo a ponte CSV–Lean: na tentativa
piloto `(a,j)=(2/5,0)`, `decide` parou em `Rat.num`, `rfl` não foi conversível e
`norm_num` excedeu 1 milhão de passos após cerca de 28 minutos. Fonte, logs,
pins, hash do `.olean` e comando de retomada estão em
`evidence/rational-boxes/c5-log2-component-validation/README.md`.

## Tentativa de ponte formal dos extremos CSV (2026-11-07, incompleta)

Foi testada a linha `(a,j)=(2/5,0)` entre o CSV de 516 caixas e
`c5RationalZetaCenteredNodeBox 512 192 896 (2/5) 0`. `decide` parou na
redução de `Rat.num`, `rfl` confirmou que a igualdade não é definicional, e
`norm_num` com `maxSteps=1000000` excedeu o limite após cerca de 28 minutos.
O pico observado foi ~7,6 GiB numa VM com ~58 GiB disponíveis. Não há
teorema-ponte compilado nem auditoria válida; `sorryAx` exibido após os erros é
recuperação do elaborador e não foi aceito como resultado. Portanto, o CSV
permanece apenas saída de `#eval`, sem uso formal nas inclusões C5. Logs,
fontes, pins e comando estão em
`evidence/rational-boxes/c5-exported-box-proof-attempt/`. Próximo passo:
fatorar e compartilhar a redução do log, da cabeça, das correções de Bernoulli
e da exponencial, medindo componentes separadamente antes de tentar as 516
igualdades.

**Registro pós-merge:** a tentativa e seus limites foram publicados como
checkpoint explicitamente incompleto pela PR #215, commit `baa5e3e`, merge na
`main` `6bfb4b14606ec1896a2d01d60be4ca54117bd128`. A main permanece com a
exportação CSV não ligada formalmente às caixas Lean e com as duas inclusões
C5 abertas.

## Tentativa inicial direta do componente `log 2` (2026-11-07, superada)

Como passo de decomposição, `#eval` exportou os extremos exatos de
`c5CenteredLog2I 512` em ~40 s. A prova aritmética desses mesmos extremos não
fechou: `norm_num` deixou metas abertas, inclusive após separar `lo`/`hi`, usar
`maxSteps=1000000` e tentar `norm_num1`. Nenhum teorema foi compilado nem
teve auditoria válida. Logs e fontes estão em
`evidence/rational-boxes/c5-log2-component-attempt/`. Esse diagnóstico foi
integrado pela PR #217, commit `e34733a`, merge na `main`
`30a615cafa3b27de40427a73cc64988c77e236d3`. A prova em blocos acima superou
esse subproblema; a ponte dos 516 extremos e a composição da fonte continuam
abertas.

## Checkpoint integrado — Bernoulli compartilhado (2026-11-07)

Na worktree `codex/c5-flatten-zeta-boxes-20261107`, a tabela incremental de
Bernoulli e a integração da tabela à caixa Euler–Maclaurin de um nó foram
provadas, compiladas em Lean 4.32 e auditadas. A caixa completa de um nó
terminou em 2:05; três nós com tabela compartilhada terminaram em 2:20. O lote
de 129 nós continua lento e foi interrompido sem largura final após 15:57.
Memória medida: cerca de 6,5 GiB usados numa VM com 64 GiB totais; não pedir
mais memória. O checkpoint parcial foi integrado pela PR #211, commit
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`, merge na `main`
`c6dd548bcb030a21bb90c1aee08023c2ca2d485f`. C5 segue incompleta. Detalhes,
comandos e logs em
`evidence/rational-boxes/c5-fast-bernoulli-table-validation.md`.

## Exportação das caixas zeta em quatro coordenadas (PR #213 integrada)

Depois do checkpoint #211, quatro sondas Lean compilaram e terminaram com
código 0. Cada uma exportou os 129 índices `j=0…128` como extremos racionais
para `a=2/5`, `901/2000`, `1099/2000` e `3/5`. O CSV reúne 516 caixas e os
logs guardam as saídas exatas, tempos e picos de memória. Esta etapa conclui a
exportação nodal de zeta; as avaliações de Gamma, completação por π,
interpolação e inclusões C5 seguem abertas. A igualdade formal do CSV com as
caixas calculadas também ainda precisa ser registrada em Lean. Evidência em
`evidence/rational-boxes/c5-centered-all-a-zeta-export-validation.md`. O
checkpoint foi integrado pela PR #213, commit de prova
`f51db20fa6fd21e08bbc2080cdd4bcb2265e2ea1`, merge na `main`
`5fe8a7b330d6a106e2b2c44781b8d0677c7ea7f3`.

## Snapshot atual — cobertura formal dos 129 nós de zeta integrada pela PR #209

**Atualizado:** 2026-11-07 UTC. O commit de prova
`05dae531d4ec10c916c340f58255f35977a3abdd` foi integrado pela PR #209 no
merge `386b654eabe4c942d6b0db46754120ab79b52fb5`. A compilação limpa dos módulos
`SigmaC5RationalNodeLogBounds`, `SigmaC5RationalNodeInstantiate` e da auditoria
passou em Lean 4.32 com `warningAsError=true`; o checker fail-closed aceitou
21 raízes com apenas `propext`, `Classical.choice` e `Quot.sound`.

`c5RationalZetaAdaptiveNodeBox_contains_at` inclui zeta nos nós
`b=j/100000`, `0≤j≤128`, para `a∈[2/5,3/5]`; o teorema conjugado cobre a parte
imaginária negativa. A escala adaptativa prova `m/2^k∈[1/2,1]` e os limites
de log/exp necessários; a cauda Euler–Maclaurin `<10^-250` permanece na caixa.
Logs limpos, hashes, pins, reprodução e falhas anteriores estão em
`evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`
e na pasta `c5-node-instantiation-clean-20261107/`.

C5 ainda está incompleta: não há extremos racionais achatados, composição com
Gamma, fator de π e expressão da fonte C2, nem prova das inclusões dos
coeficientes nas caixas O3. Próxima obrigação: instanciar precisão e achatar as
caixas, compor a fonte original mantendo sua cabeça e cauda, provar as duas
inclusões O3 e então auditar os sinais. A lei distância × profundidade e os
novos cadernos continuam adiados.

**Atualizado:** 2026-11-07
**Última integração de código:** PR #209, commit de prova
`05dae531d4ec10c916c340f58255f35977a3abdd`, merge
`386b654eabe4c942d6b0db46754120ab79b52fb5`. A cobertura adaptativa dos 129 nós está integrada;
O4/C5 continua explicitamente incompleta.
**Integrações anteriores:** C1–C4, O3, a ponte Gamma de núcleo racional e o checkpoint Euler–Maclaurin de ordem alta estão integrados. A PR #198, commit de prova `a1646a1837603aee7d03384016ae514a7f7c820a`, foi mesclada na `main` em `36cba9d805bc3274538cdc93bd0a3702154edcb2`; a PR #205, commit de prova `61ddab8dbd5e669b2185a23c0900d2cba22dbf7a`, foi mesclada em `b56a90bceac12248bc5b8e6c2a247849ec885d6e`. O checkpoint integrado pela PR #209 cobre zeta nos 129 nós, mas O4/C5 segue aberta: falta compor a fonte original e provar a inclusão formal dos coeficientes C2 nas caixas.

**Checkpoint integrado — avaliador racional genérico (PR #207):** o commit de
prova `fb8bb31ed1fcbb4d1d9c88aceea1dd83539935df` foi mesclado na `main` em
`27a61e6bebcce178b81b961f507400ed77b96d3b`. `SigmaC5RationalNodeEval.lean`
fatoriza a correção Bernoulli de `emZetaHighRHS 100 300` em aritmética
racional-complexa e prova `c5RationalZetaNodeBox_contains` sob condições
explícitas de log/exp para a cabeça e a base 100. A cauda exata é mantida e
absorvida com erro `<10^-250`. Build Lean 4.32 com warnings como erros e
auditoria fail-closed de dez roots passaram, só com axiomas padrão. O
checkpoint foi publicado explicitamente como incompleto: não há instanciação
concreta nos 129 nós, composição com Gamma/fator de completação ou inclusão
dos coeficientes nas caixas O3. Evidência, pins e hashes:
`evidence/rational-boxes/c5-rational-node-evaluator-validation.md`.

Os verificadores racionais dos dois JSONs Momentos também foram repetidos: os
sinais condicionais são `+++++++++++-` em `99/2000` e `+++++++++-` em `1/10`.
Esses sinais continuam condicionados às caixas e não demonstram sua inclusão
na fonte C2.

**Reprodução de 2026-11-06:** as três configurações prescritas foram executadas novamente em uma cópia temporária do checkout Momentos com o patch `gmpy2.mpz`→`int` já preservado em `evidence/interval-certificate/momentos-gmpy2-compat.patch`. As inclusões numéricas experimentais foram geradas, e o verificador independente por frações racionais exatas passou: `+++++++++++-` para `d=99/2000` nas duas configurações e `+++++++++-` para `d=1/10`. Isso continua **condicional** às caixas experimentais: não certifica por Lean que os coeficientes da fonte C2 estejam nelas. Comandos, logs e limites estão em `evidence/interval-certificate/reproduction-2026-11-06.md`.

**Checkpoint integrado de Euler–Maclaurin de ordem alta (2026-11-06):** `SigmaC5EulerMaclaurin.lean` prova a identidade da `riemannZeta` original no quadrante superior `Re(s)>0, Im(s)>0` e nos pontos reais positivos `s≠1`. Com `N=100`, `P=300`, limita por `<10^-250` a cauda nos nós com `2/5≤Re(s)≤3/5` e `|Im(s)|≤128/100000`. Build limpo Lean 4.32 e auditoria fail-closed de oito raízes passaram; somente os axiomas padrão foram usados. PR #205, commit de prova `61ddab8dbd5e669b2185a23c0900d2cba22dbf7a`, merge `b56a90bceac12248bc5b8e6c2a247849ec885d6e`; o GitHub não reportou checks hospedados. A validação, pins, comandos, logs e hashes estão em `evidence/rational-boxes/euler-maclaurin-high-order/`. Esta etapa **não** avalia os 129 nós, não certifica caixas da fonte C2 e não fecha O4.

## Snapshot atual — ponte Gamma de núcleo racional integrada pela PR #198

`SigmaC5GammaRationalCore.lean` prova, para entradas racionais, que
`gammaFinite N T z` é exatamente `T^z` vezes uma soma finita em `ℚ+iℚ`.
`gammaFiniteInterval_contains` combina essa soma exata com o avaliador de
`T^z`; `gamma3072Interval_contains` inclui a Gamma verdadeira inflando a caixa
por `10^-259`, usando `gamma_finite_3072_620_error`. A expansão preserva o
cancelamento da soma finita como aritmética racional exata.

Build Lean 4.32 com warnings como erros e auditoria fail-closed de seis raízes
passaram; os 11 relatórios combinados usam apenas `propext`, `Classical.choice`
e `Quot.sound`. Logs, comando, pins e hashes estão em
`evidence/rational-boxes/c5-gamma-rational-core-validation.md`. O teorema é
genérico: ainda não calcula extremos racionais nos 129 nós, não certifica os
limites da potência exponencial em cada nó, não avalia zeta/Hurwitz e não prova
as inclusões dos coeficientes C2 nas caixas O3. O4 permanece aberta.

Base anterior: `dcdcf9c4ac949376fe49a8ddebfabf4fd5f8a5cd`. PR #198 publicada
com commit de prova `a1646a1837603aee7d03384016ae514a7f7c820a`, merge na `main`
`36cba9d805bc3274538cdc93bd0a3702154edcb2`. Não houve checks hospedados; a
compilação limpa e a auditoria local estão registradas em
`evidence/rational-boxes/c5-gamma-rational-core-validation.md`.

**Checkpoint atual — cota analítica explícita integrada (2026-11-06):** `CarrySigmaObstruction.displacedProductC_norm_le_10pow13_on_ball_39` prova `‖displacedProductC d z‖ ≤ 10^13` para `|d|≤1/10` e `z∈ball(0,39/100)`. O wrapper `10^100` da PR #191 continua disponível. O build limpo Lean 4.32 e a auditoria fail-closed de quatro raízes passaram; somente `propext`, `Classical.choice` e `Quot.sound` aparecem. Detalhes, hashes e logs estão em `evidence/rational-boxes/analytic-bounds-10pow13-validation.md`. Com o contorno `38/100`, a análise exata dá erro de interpolação `<10^-501` e amplificação do erro Gamma `<10^-135`.

**Checkpoint integrado — faixa racional de π (2026-11-06):** `SigmaC5PiBounds.lean` prova o resto da série alternada para `arctan` e combina as truncações `N=170` em `1/5` e `N=55` em `1/239` com a identidade de Machin para obter uma faixa racional exata de `Real.pi`. Build limpo Lean 4.32 passou; a auditoria das duas raízes usa somente `propext`, `Classical.choice` e `Quot.sound`. PR #193, commit de prova `45bc923`, merge na `main` `2567ab0204c46c4ce04fca601c99e47e810e18b9`. Fonte, comandos, pins, logs e hashes estão em `evidence/rational-boxes/c5-pi-bounds-validation.md`. O checkpoint é preparatório: faltam as avaliações da fonte original nos 129 nós e a inclusão dos coeficientes C2 nas caixas; nenhuma caixa foi certificada nesta etapa.

**Checkpoint integrado — fator de completação dependente de π (PR #195):** `SigmaC5PiInterval.lean` transforma a faixa racional de π em faixa intervalar de `log π` com o `Interval.log1` certificado. `SigmaC5PiExp.lean` transporta essa faixa ao fator original `Complex.exp (-(s/2) * log π)` via `expCr`, para qualquer caixa `s` com o limite de norma exigido. Build limpo e auditoria das cinco raízes passaram em Lean 4.32; apenas axiomas padrão aparecem. PR #195, commit de prova `321ae94`, merge na `main` `0032b10295bfeaadb29d0387f9b99dde9b160ac3`. Logs, pins, hashes e comando estão em `evidence/rational-boxes/c5-pi-completion-factor-validation.md`. Este subpasso não avalia Gamma, a cauda C2 ou os 129 nós.

**Próxima etapa registrada na integração da PR #207 (superada):** instanciar as condições `hhead`/`hbase` do avaliador para `j=0,…,128`, `b=j/100000` e as partes reais `2/5`, `901/2000`, `1099/2000` e `3/5`; extrair retângulos racionais concretos. Essa cobertura de zeta foi provada no checkpoint integrado pela PR #209. Ainda falta combinar zeta, Gamma, fator dependente de π e a fonte C2 original, mantendo sua cabeça e cauda exata, para provar as inclusões O3.

**Checkpoint de graus 2–14 (2026-11-06):** `c5LagrangeBasis_zeroIndex_coeff_abs_le_two_pow`, `c5LagrangeBasis_nonzeroIndex_coeff_abs_le_weight`, `c5InterpolationCoeffAbsSum_le_four_mul_two_pow` e `c5InterpolationWeightSum_lt_ten_145` formalizam a cota uniforme simbólica. Build limpo: `c5-interpolation-degree2-14-final-clean-build.log`, `BUILD_EXIT=0`. A auditoria das 23 raízes aceita apenas `propext`, `Classical.choice` e `Quot.sound`; logs e hashes estão preservados. O checkpoint permanece explicitamente incompleto e não prova inclusão de caixas.
**Checkpoint de grau um (2026-11-06):** a alteração simbólica de `SigmaRationalInterpolation.lean` passou build Lean 4.32 limpo e auditoria fail-closed de 21 raízes. Logs e hashes estão em `evidence/rational-boxes/degree1-weight-bound-validation.md`; tentativas anteriores incompletas e a prova rejeitada com `native_decide` foram mantidas como histórico.
**Publicação do limite de grau um:** PR #185, commit de prova `90a208df98e74a7c5ab1fe83a9ef0fc90c3d3cb6`, merge `c840ba35711ac8f938fa24c191f2af60f505480d`. O checkpoint explicitamente incompleto foi publicado separadamente pela PR #184, merge `5528ddc8093a22682c87f3f9c6575e30e90a7011`.
**Branch C5 de trabalho:** o passo estrutural de grau um foi publicado no commit `0a188c9d71a1a54bdf446ec753609fdde8326bc8`, integrado pela PR #181. A branch remota de prova foi removida após o merge; retomar a partir da `main` atual e abrir uma branch nova.
**Main geometry no início da auditoria O4:** `1bc7318915c3e625ad228c89ff8c300cb07e52c5` (merge da PR #168).
**Última prova geometry integrada:** PR #187, limite dos pesos escalados de graus 2–14, merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
**Registro de estado anterior à PR #177:** PR #176, merge `ac84c9302ae608e39c742f856ad361921653f268`.
**Última prova integrada:** PR #187, limites dos pesos escalados de graus 2–14, merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
**Main geometry após a PR #187:** `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
**Checkpoint de estado pós-PR #181:** PR #182, merge `8f8b9da2b8c1e8f3b8d1290608c8b2abffe9c285`.
**Main geometry no checkpoint de estado:** `8f8b9da2b8c1e8f3b8d1290608c8b2abffe9c285`.
**Repositório geometry no checkout de pesquisa original:** branch `agent/native-moving-schur-sigma`, HEAD `9392ebac9930f5d11c56f595556080e8ab1de809`, com logs/caches não rastreados preservados. A `main` remota consultada após a PR #187 está em `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
**Repositório Momentos:** checkout local `main` em `05c9314d59306383baa55ed3be80ab950e799e97`; branch remota de pesquisa `origin/research/sigma-pade-dimension-depth-20261104` em `68c9b5f0a196289e28a8e5586146707d27df6b75`. PR #2 está OPEN e não foi integrada.

## Inventário de trabalho anterior

- C2, C3 e C4 constam integradas à main geometry. C4 está documentada em `mission-sigma-sign-20261105/evidence/c4-source-bezout/VALIDATION.md`.
- `SigmaSourceBezout.lean` já define `completedSigmaDisplacedSourceCoefficient` e `completedSigmaDisplacedMoment`; prova `C_d·H_d=-C_d′`, `H_d(n)=2*completedSigmaLogJet d n`, e `c₀>0` para os deslocamentos no domínio. O fator 2 deve permanecer explícito.
- Foi criado `SigmaFiniteCoefficientSignTransport.lean`. Em Lean 4.32 prova a recorrência polinomial sem divisão, a identidade exata com `CarrySigmaPade.sigmaPadeD` original e os transportes de sinais positivo/negativo. `SigmaFiniteCoefficientSignTransportAudit.lean` registra os quatro `#print axioms`; footprint: `propext`, `Classical.choice`, `Quot.sound`.
- A Fase 1 foi integrada pela PR #165, com commit de prova `1250a9989e596fa250304d8ec8fd3ae45897e589` e merge `75691edf0e74cc643f098213f60b684476132175`. Não houve status checks hospedados; build Lean 4.32 e auditoria local estão preservados em `evidence/`.
- Os dois JSONs racionais passaram no verificador exato, produzindo `+++++++++++-` e `+++++++++-` condicionais às caixas. As três gerações prescritas foram reproduzidas após ajuste local de compatibilidade (`gmpy2.mpz`→`int`) no checkout Momentos isolado. Patch e falha original estão preservados em `evidence/interval-certificate/`; a branch remota Momentos não foi alterada.
- A ponte geométrica `canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar` foi consultada na revisão carry pinada `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O avaliador usa Hurwitz somente para avaliar a cauda exata e mantém a cabeça C2 e a completação original.
- O diretório `research/c3-fourteenth-tail/` e seus módulos dizem respeito a outro certificado finito; foram observados durante a busca e não são reutilizados sem prova de correspondência à fonte C2 desta missão.
- Há várias worktrees com alterações/logs paralelos. A branch de pesquisa original e caches/logs não rastreados foram mantidos intactos; C5 usa worktree nova.

## O que está provado / condicional / pendente

**PROVADO e integrado (contexto):** C2 eventual em `d=1/5`; C3 setores par e ímpar; C4 recorrência original e equivalência Bézout. Isso não prova os sinais finitos desta missão em `d=99/2000` ou `d=1/10`.

**PROVADO em Lean nesta branch:** a recorrência `p_n` sem divisão, a identidade `p_s p_(s+2)-p_(s+1)^2 = 4*c_0^(2*s+4)*sigmaPadeD d s` e os dois lemas genéricos de transporte de sinal. Lean 4.32 e auditoria de axiomas passaram.

**PROVADO CONDICIONALMENTE e integrado pela PR #167:** as caixas exatas são propagadas pela recorrência polinomial da Fase 1; os limites inferiores dos menores são positivos para `s<11` em `99/2000` e para `s<9` em `1/10`, e os limites superiores finais são negativos em `s=11` e `s=9`. Sob hipóteses explícitas de inclusão (`sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`), isso prova os sinais de `sigmaPadeD` original. Merge: `fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`. Build limpo e auditoria de 13 raízes passaram; só aparecem `propext`, `Classical.choice`, `Quot.sound`. Ver `evidence/rational-boxes/VALIDATION.md`.

**PENDENTE:** provar que os coeficientes verdadeiros da fonte C2 original pertencem às caixas; depois compor os dois teoremas finais incondicionais. A primeira obrigação aberta agora é O4, não O3.

**O4 — avanço de infraestrutura:** os módulos existentes `ZetaLean.Rigor`, `ZetaLean.IntervalExp` e `ZetaLean.IntervalCExp` foram recompilados em Lean 4.32 com warnings como erros. Aritmética retangular racional, `log` real, `exp` real/complexo e `m^{-s}` têm inclusões kernel-checked. Quatro raízes foram auditadas e dependem apenas de `propext`, `Classical.choice`, `Quot.sound`.

O checkpoint reprodutível dessa auditoria foi integrado pela PR #169; merge na main `75782fb8b7fb00bd273bd99f78c337f98439e934`. Os logs, comandos, hashes de fontes e `.olean` agora estão rastreados em `evidence/rational-boxes/`.

**Subpasso Gamma integrado pela PR #171:** `SigmaC5Gamma.gamma_finite_512_error` demonstra erro `≤10⁻³²` para `gammaFinite 512 81` no domínio `1495/20000 ≤ Re(z) ≤ 1`; build e auditoria de oito raízes passaram.

**Subpasso Gamma de precisão alta integrado pela PR #173:** `gamma_finite_1024_240_error` demonstra erro `≤10⁻⁹⁹` para `gammaFinite 1024 240` no mesmo domínio. Build Lean 4.32 com warnings como erros e auditoria de dez raízes passaram. Merge: `72586b6223579ee1b37a6077ad6f2a0eceaf919c`. Logs e hashes estão em `evidence/rational-boxes/`.

**Subpasso Gamma para interpolação racional integrado pela PR #175:** `gamma_finite_3072_620_error` demonstra erro `≤10⁻²⁵⁹` para `gammaFinite 3072 620`, no domínio `1495/20000 ≤ Re(z) ≤ 1`. Build Lean 4.32 e auditoria de doze raízes passaram. Merge: `992ab31c3aacdf3b95b3c02fe58f5f3d529c0cec`. Logs e hashes estão em `evidence/rational-boxes/`.

**Estado corrigido do subproblema Gamma:** um piloto novo certifica o núcleo racional de `gammaFinite 1024 240` em `(a,b)=(1/5,0)` por 16 blocos de 64 parcelas. A caixa `[S/2^1024,(S+16)/2^1024]×{0}` está provada, mas ainda não inclui `240^z` nem `gammaFinite` ou Gamma completa. O erro analítico `gamma_finite_1024_240_error` já está integrado; a composição de potência, caixa do ponto e extensão aos nós ainda falta. Evidência: `evidence/rational-boxes/c5-gamma-core-node-pilot-20261107/README.md`.

**Identidade algébrica de interpolação:** `SigmaRationalInterpolation.lean` define os 129 nós `j²`, prova que são distintos e formaliza a reconstrução exata de polinômios racionais de grau menor que 129 e a fórmula dos coeficientes pela interpolação de Lagrange. Build Lean 4.32 limpo e auditoria atualizada de 21 raízes passaram; apenas `propext`, `Classical.choice` e `Quot.sound` aparecem.

**Grau zero dos pesos provado:** o coeficiente constante da base de Lagrange em `j=0` é `1`, as demais bases têm coeficiente constante `0`, e `c5InterpolationWeightSum_zero_eq_one` conclui que a soma absoluta do peso escalado de grau zero é exatamente `1`.

**Pesos de graus 0–14 provados:** grau zero tem soma absoluta exatamente `1`; grau um satisfaz `<10^11`; para cada `2≤n≤14`, `c5InterpolationWeightSum_lt_ten_145` prova `<10^145`. A prova de grau um integrada pela PR #185 está descrita em `degree1-weight-bound-validation.md`; a prova local mais recente está em `degree2-14-weight-bound-validation.md`. A cota analítica da fonte e a inclusão C2 nas caixas continuam abertas.

**Publicação do grau um:** PR #185, merge `c840ba35711ac8f938fa24c191f2af60f505480d`; validação limpa e auditoria de 21 raízes em `evidence/rational-boxes/degree1-weight-bound-validation.md`. O4 continua aberta.

## Checkpoint O4 — domínio analítico da fonte deslocada (2026-11-06)

**PROVADO localmente em Lean 4.32:** `SigmaC5SourceAnalytic.lean` estabelece
`displacedProductC_analyticOnNhd_ball` para `|d|≤1/10` e disco aberto de raio
`2/5`, com especializações em `99/2000` e `1/10`. A prova transporta os dois
argumentos da característica completada original ao domínio de altura do
Carry; não muda a fonte C2.

Build limpo com `warningAsError=true` passou. O checker fail-closed auditou as
quatro declarações públicas e aceitou somente `propext`, `Classical.choice` e
`Quot.sound`. Fonte, log da tentativa inicial com cache errado, log da execução
que passou, saída do checker e hashes estão em
`evidence/rational-boxes/source-analytic-domain-validation.md`.

Este resultado prova apenas analiticidade no domínio. **Não** estabelece a
cota de módulo necessária à interpolação, não certifica os valores nos 129 nós
e não prova as inclusões dos coeficientes nas caixas. A obrigação O4 continua
aberta. Próxima obrigação: provar uma cota numérica explícita a partir da
completação C2 original, tratando os cancelamentos nos pontos `s=0` e `s=1`.

**Git publicado:** PR #189, commit de prova
`e0272bfc9099031cb127ea0db8874900d9e8eca1`, merge na `main`
`3513a3b3854b105419d4f2cef245efac7ce88ba0`. A branch pós-merge de estado é
`codex/c5-state-after-pr189-20261106`. Não há PR aberta.

## Validação reproduzida

- A: `d=.0495`, `L=0`, `N=1024`, `r/R=.30/.40`: `+++++++++++-`.
- A independente: `d=.0495`, `L=12`, `N=512`, `r/R=.20/.40`: `+++++++++++-`.
- B: `d=.1`, `L=12`, `N=512`, `r/R=.15/.30`: `+++++++++-`.
- Os logs, JSONs, hashes e patch de compatibilidade estão em `evidence/interval-certificate/`.
- Build limpo e auditoria dos módulos de transporte algébrico estão em `evidence/build-transport-clean.log` e `evidence/axiom-audit-transport-clean.log`; build e auditoria de O3 estão em `evidence/rational-boxes/`.

## Regras de estado

Nenhuma caixa JSON será elevada a fato sobre os coeficientes sem uma prova de inclusão. O3 conclui os sinais apenas sob as hipóteses explícitas de caixa; O4 ainda bloqueia os teoremas incondicionais dos dois deslocamentos.
