# Próximos passos — C5

## Estado atual e próxima prova — prefixo Bernoulli de 64 entradas integrado (2026-11-08)

- A PR #300 integrou `c5BernoulliPrimeTable_64_eq_data` (commit `509e773`, merge `90e2f571efb482993682a05ccc938ee9aef388e5`). As primeiras 64 entradas (índices 0–63) coincidem formalmente com a recorrência, com o certificado 0–32 como base.
- Reprodução limpa passou: sonda, tabela, certificados 32 e 64, comparação racional exata dos 601 valores e auditoria isolada. Axiomas: somente `propext`, `Classical.choice`, `Quot.sound`. Certificado 0–64: 14:09, pico RSS 4.8 GiB.
- A validação é parcial: 64 valores têm igualdade formal; 537 ainda precisam de prova em blocos. Nenhuma ligação formal das caixas CSV de zeta nem inclusão da fonte C5 foi fechada.
- **Próximo passo concreto:** provar as primeiras 96 entradas (prefixo 0–95) usando o resultado até 64, depois seguir por blocos até 601. Só então retomar a igualdade Lean de uma caixa de zeta exportada. Evidência: `evidence/rational-boxes/c5-bernoulli-data-prefix64-20261108/README.md`.

## Estado atual e próxima prova — prefixo Bernoulli 0–32 integrado (2026-11-08)

- PR #298 integrou `c5BernoulliPrimeTable_32_eq_data` na `main` (commit `1ed4a00`, merge `171c19681482312bf71bffdcd23b24a728edf04b`). O primeiro bloco de 32 da tabela recursiva tem igualdade formal com os dados literais.
- A reprodução limpa recompila sonda, tabela, certificado e auditoria; compara exatamente os 601 valores da sonda com os 601 literais. Resultado: `CLEAN_BUILD=PASS`, `DATA_TABLE_CHECK=PASS`, `AXIOM_AUDIT=PASS`; apenas os axiomas padrão `propext`, `Classical.choice`, `Quot.sound`.
- A validação é parcial: só os primeiros 32 valores têm certificado formal. Os outros 569 ainda precisam de provas em blocos; nem a ligação CSV–Lean das caixas de zeta nem as inclusões da fonte C5 foram fechadas.
- **Próximo passo concreto:** provar a igualdade do prefixo 64 a partir do prefixo 32 e da recorrência; repetir em blocos até 601. Em seguida, retomar a igualdade Lean da menor caixa de zeta exportada. Evidência e comandos: `evidence/rational-boxes/c5-bernoulli-data-prefix32-20261108/README.md`.

## Estado atual e próximo passo — par complexo de `d=1/10` integrado (2026-11-08)

- Estão integrados os nós `Γ(901/4000 + 3i/20)` e `Γ(1099/4000 + 3i/20)` para `d=99/2000`, e `Γ(1/5 + 3i/20)` e `Γ(3/10 + 3i/20)` para `d=1/10`. Os pontos reais `Γ(1/5)` e `Γ(901/4000)` também têm caixas certificadas.
- PR #296 prova `CarrySigmaObstruction.c5GammaComplexNodeDOneUpperComplexBox_contains`. O limite refinado `|Interval.logQ 384 8 240| ≤ 10` torna válida a avaliação de potência com raio 8; a caixa Gamma mantém o resto formal `gamma_finite_1024_240_error ≤ 10⁻⁹⁹`.
- Seis módulos passaram em Lean 4.32.0 com `warningAsError=true`; 16 relatórios usam apenas `propext`, `Classical.choice`, `Quot.sound`, sem `sorryAx`, axiomas próprios ou `native_decide`. Pico RSS: 8.4 GiB; reprodução limpa aprovada.
- PR #296 integrou o commit `e986390937265fc1bb759140ed7fb6d80d23eadf` no merge `113ed1517fff040f4fc619cf7d5086c57f137427`. Evidência completa: `evidence/rational-boxes/c5-gamma-d1-upper-complex-node-20261108/README.md`.
- Próximo passo concreto: ligar formalmente, por nó, as 516 caixas de zeta exportadas (129 × quatro coordenadas) às caixas usadas no cálculo Lean. O CSV e `#eval` comprovam exportação/cobertura, não a igualdade necessária; a expansão Euler–Maclaurin de ordem 600 está provada e integrada.
- Em seguida, avançar os demais nós Gamma e compor as caixas com o fator nativo e quadraturas para provar `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. C5 permanece incompleta.

## Checkpoint anterior — caixa `Γ(1/5)` (PR #285 integrada)

`CarrySigmaObstruction.c5GammaCoreFirstNodeBox_contains` está integrada no merge `832b201b6907c6682aa9657c3e4ff9da6dd40254`; evidência em `evidence/rational-boxes/c5-gamma-first-node-20261107/README.md`.

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

## Checkpoint auxiliar — estágio Taylor 18 integrado pela PR #275

`c5RoundedExpStateC_stage18_correct` passou em Lean 4.32.0 com
`warningAsError=true`; as cinco raízes auditadas mostram somente axiomas
padrão. O commit `eb7209321914de6733de0bd160e1c64633924dba` entrou na `main` pelo merge `df23788957cb17b16832d5f4c9e47fd8aa12d68f`.
O GitHub não reportou checks hospedados. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage18-20261107/README.md`.
O checkpoint cobre apenas `n≤18` no nó `(2/5,0)`.

Este checkpoint é auxiliar. A transição `n=18→19` foi retomada após a prova do termo `m=1` e passou localmente; os próximos passos ativos voltam à composição da caixa zeta exportada e às inclusões da fonte C2. Estender o Taylor além de `n=19` deve responder a uma dependência concreta dessa composição.

C5 continua incompleta.

## Checkpoint anterior — estágio Taylor 17 integrado pela PR #273

O passo `n=16→17` foi integrado no merge `41164de6cf0042594833bae02cdab2ce4cd11aae`; evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage17-20261107/`.

## Checkpoint anterior — estágio Taylor 16 integrado pela PR #271

O passo `n=15→16` foi integrado no merge `795caa0eebfaa61874c1fff22c683fb85bdf941a`; evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage16-20261107/`.

## Checkpoint anterior — estágio Taylor 15 integrado pela PR #269

O passo `n=14→15` foi integrado no merge `fe6d5c238ba9ee796dc5ef56880aa60e89899c63`; evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage15-20261107/`.

## Checkpoint anterior — estágio Taylor 14 integrado pela PR #267

O passo `n=13→14` foi integrado no merge `b1a7c9b14eb1352cc470508fdb2bf9a8baaea56a`; evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage14-20261107/`.

## Checkpoint anterior — estágio Taylor 13 integrado pela PR #265

O passo `n=12→13` foi integrado no merge `52c57108c74cb5f7f12bdbd94ca616f3bba8cf2a`; evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage13-20261107/`.

## Checkpoint anterior — estágio Taylor 12 integrado pela PR #263

O estágio `n=11→12` no nó `(2/5,0)` foi integrado pelo merge
`4b5b6a0aebd54798e6a26b2eda69994589c78668`; sua evidência está em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage12-20261107/`.

## Atualização — estágio Taylor 10 integrado pela PR #259

`c5RoundedExpStateC_stage10_correct` passou em Lean 4.32.0 com
`warningAsError=true`; cinco declarações auditadas dependem somente de axiomas
padrão. A evidência está em
A PR #259 integrou o commit de prova
`5dd4f4874a192e83af26640f412f81f42239487b` no merge
`d68eec91118e2cdcb89fced66a14062ef6170cf9`; o GitHub não reportou checks
hospedados. O checkpoint cobre apenas `n≤10` no nó `(2/5,0)`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage10-20261107/README.md`.

1. Estender a recorrência para `n=11` e seguir até `n=192`.
2. Certificar as quadraturas e a caixa nodal completa.
3. Provar a ponte CSV–Lean, as inclusões da fonte C2 e os sinais finais.

C5 continua incompleta.

## Atualização — estágio Taylor 9 integrado pela PR #257

`c5RoundedExpStateC_stage9_correct` passou em Lean 4.32.0 com
`warningAsError=true`; cinco declarações auditadas usam somente axiomas
padrão. A evidência está em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage9-20261107/README.md`.
A PR #257 integrou o commit de prova
`62c9fbd7b04034f21ccf0336abf0d83d8c6a6592` no merge
`9655308b17dbf565d272f7578545bb68b7b0b867`; o GitHub não reportou checks
hospedados. O alcance é `n≤9` no nó `(2/5,0)`.

1. Provar `n=10` e continuar até `n=192`.
2. Certificar quadraturas e a caixa nodal completa.
3. Provar a ponte CSV–Lean, as inclusões da fonte C2 e os sinais finais.

C5 continua incompleta.

## Atualização — estágio Taylor 8 integrado pela PR #255

`c5RoundedExpStateC_stage8_correct` passou em Lean 4.32.0 com
`warningAsError=true`; cinco declarações auditadas mostram somente axiomas
padrão. Fonte, probe, logs, pins e hashes estão em
A PR #255 integrou o commit de prova
`96f5f5709829282756bc8c8a2b52a80290c96735` no merge
`29d363068d52c62c37afc3896f6b3d46f734f16b`; o GitHub não reportou checks
hospedados. O checkpoint cobre apenas `n≤8` no nó `(2/5,0)`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage8-20261107/README.md`.

1. Estender a recorrência para `n=9` e seguir até `n=192`.
2. Certificar as quadraturas e a caixa nodal completa.
3. Provar a ponte CSV–Lean, as inclusões da fonte C2 e os sinais finais.

C5 continua incompleta.

## Atualização — estágio Taylor 7 integrado pela PR #253

`c5RoundedExpStateC_stage7_correct` passou em Lean 4.32.0 com
`warningAsError=true`; cinco declarações auditadas exibem somente axiomas
padrão. Fonte, probe, logs, pins e checksums estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage7-20261107/README.md`.
A PR #253 integrou o commit de prova
`a08a5c9c5a1d02fc33b3207ef2be3d362d526de8` no merge
`952fcd76093681f3feacc540bb0db9c49bfc6034`; o GitHub não reportou checks
hospedados. O checkpoint cobre apenas `n≤7` no nó `(2/5,0)`.

1. Estender a recorrência para `n=8` e continuar modularmente até `n=192`.
2. Certificar as quadraturas e a caixa nodal completa.
3. Provar a ponte CSV–Lean, as inclusões da fonte C2 e os sinais finais.

C5 permanece incompleta.

## Atualização — estágio Taylor 6 integrado pela PR #251

`c5RoundedExpStateC_stage6_correct` passou em Lean 4.32.0 com
`warningAsError=true`; as cinco declarações auditadas têm somente axiomas
padrão. A evidência integral está em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage6-20261107/README.md`.
A PR #251 integrou o commit de prova
`e6c9ef307c69c59a8e665232b4b0271c481d8fcd` no merge
`7b61a5ceb0d8567c33fe27a5810d493f4640ed69`; o GitHub não reportou checks
hospedados. O checkpoint cobre somente `n≤6` do nó `(2/5,0)`.

1. Estender a recorrência do nó m=2 para `n=7`, seguindo o padrão modular dos
   estágios anteriores.
2. Continuar até `n=192`; certificar quadraturas e a caixa nodal completa.
3. Provar a ponte CSV–Lean, as inclusões da fonte C2 e os sinais finais.

C5 continua incompleta; o estágio atual não fecha a fonte C2 nem as janelas
negativas finais.

## Atualização — nó m=2 validado até n=5 (PR #249 integrada)

`c5RoundedExpStateC_stage5_correct` compilou em Lean 4.32.0 com warnings como
erros e a auditoria das cinco declarações retornou apenas axiomas padrão. O
passo usou `1/4! = 1/24` e a multiplicação de intervalos de sinais mistos.
Evidência em `evidence/rational-boxes/c5-m2-dirichlet-term-stage5-20261107/README.md`.

A PR #249 integrou este checkpoint, commit de prova `1782048f05c43fc31e491fa7192105235b34a14e`, merge na `main`
`58b9a61532f79f6aa51ebfb48edaacf728be3738`; não houve checks hospedados.
Próximo: `n=6`. Depois, ainda será necessário provar
os demais termos, as quadraturas do avaliador, a caixa nodal completa, a ponte
das 516 caixas e as inclusões da fonte C2. C5 segue incompleta.


## Atualização — nó m=2 provado até n=4 (PR #247 integrada)

`c5RoundedExpStateC_stage4_correct` passou o build Lean 4.32.0 com
`warningAsError=true` e a auditoria das cinco raízes, que mostra somente
axiomas padrão. O coeficiente `1/3!`, o produto de sinais não-positivos e a
soma foram certificados em aritmética racional. A evidência está em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage4-20261107/README.md`.

A PR #247 integrou esse checkpoint, commit de prova `7b355ce2349a242c133caf8d71b777c2a186c0a0`, merge na `main`
`ab6d5f1923770d4db830ba9ebf2fbc17c9626149`; não houve checks hospedados.
Próximo passo: provar `n=5` pela mesma decomposição. Ainda faltam os estados até `n=192`, as quadraturas do avaliador,
a igualdade com a caixa nodal completa, a ponte das 516 caixas e as inclusões
C2. C5 continua incompleta.


## Atualização — nó m=2 validado até n=3 (PR #245 integrada)

`c5RoundedExpStateC_stage3_correct` compila em Lean 4.32.0 com warnings como
erros e foi auditado com cinco declarações, somente axiomas padrão. A prova
certifica a transição `n=2→3` no nó `(2/5,0)`, incluindo a multiplicação real
de sinais mistos e o termo escalado por `1/2`. Evidência e reprodução estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage3-20261107/README.md`.

A PR #245 integrou este checkpoint, commit de prova `e264aea05ac6036dea612c5e9ca97c8c7cc81495`, merge na
`main` `727b3920d12e0979c5f722a04732fb346fc880d8`; não houve checks
hospedados. Próximo passo: provar `n=4` e
confirmar que o formato por estágios se mantém manejável. Depois, ainda será
preciso chegar a `n=192`, validar as quadraturas do termo nodal, ligar as 516
caixas à fonte C2 e provar as inclusões `sigmaC00495SourceBoxes` e
`sigmaC01SourceBoxes`. C5 continua incompleta.


## Atualização local — estado do nó m=2 até n=2 compilado (2026-11-07)

A primeira fatia da ponte CSV–Lean para `(a,j)=(2/5,0)` passou localmente:
`c5RoundedExpStateC_stage2_correct_refined` prova a recorrência de Taylor até
`n=2`, partindo do log `2` exportado e do argumento com quatro metades. Lean
4.32.0, `warningAsError=true`, compilação e auditoria de axiomas passaram.
A evidência reprodutível está em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage2-20261107/README.md`.
A PR #243 integrou esse checkpoint, commit de prova
`86d42067db230b661321190ca397bb496e855186`, merge na `main`
`20c30cec4b3964fc063d8eb3c93e09a41d319cfc`; não houve checks hospedados. O
build de `n=192` e o teorema para o termo completo continuam abertos.

Próximo passo: provar `n=3` com multiplicação de intervalos de sinais mistos,
sem voltar à simplificação monolítica que falhou. Se o método por estágios for
sustentável, estender ao estado `n=192`; depois compor as quatro quadraturas da
caixa de Dirichlet e provar sua igualdade com a avaliação nodal completa. A
obrigação maior permanece ligar formalmente as 516 caixas à fonte C2 e provar
as inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. C5 segue
incompleta.


## Estado anterior — recorrência genérica integrada; ponte CSV–Lean próxima

`c5RoundedExpC_zero_stage_2_to_192_closed_form` prova os estágios 2 a 192 na
entrada zero por uma fórmula fechada, em Lean 4.32.0. Build com warnings como
erros e auditoria separada passaram com somente axiomas padrão. A evidência e o
comando de reprodução estão em
`evidence/rational-boxes/c5-generic-exp-recurrence-20261107/`. A PR #239
integrou o checkpoint: commit de prova
`be04221f5eb4a174804fb96c9011d0b58bfc2642`, merge na `main`
`8c3691e59f9280864b93c4868eb465dbdad6da2c`. O GitHub não reportou checks
hospedados.

O próximo passo é a ponte formal CSV–Lean, seguida da
composição Gamma/π/fonte C2 e das inclusões `sigmaC00495SourceBoxes` e
`sigmaC01SourceBoxes`. C5 continua incompleta.

## Checkpoint recente — replay numérico preservado (2026-11-07)

As três configurações intervalares foram repetidas: `d=0.0495` com 1024 nós e
com 512 nós/corte 12, e `d=0.1` com 512 nós/corte 12. O erro inicial sem patch
(`gmpy2.mpz` não aceito por `Decimal`) e as três execuções corrigidas na cópia
temporária foram preservados em
`evidence/interval-certificate/reproduction-2026-11-07.md`. O checker exato
confirmou os sinais condicionais já arquivados. Isso não fecha a inclusão
formal dos coeficientes nem muda as obrigações C5.

O registro e os artefatos foram integrados pela PR #237, merge
`5fe7837e0f9509950aeb95777bdd220d68835ad8`; o GitHub não reportou checks
hospedados.

## Histórico — prova genérica da recorrência

O núcleo `m = 1` já está formalizado e compilado: o log centrado vira a caixa
exata `0`, o argumento do termo de Dirichlet vira `0`, e a exponencial
arredondada preserva a potência nula, a soma unitária e o resto de Taylor
explícito. Os sete teoremas auditados usam somente axiomas padrão. A evidência,
os pins e os comandos estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.

O núcleo do nó `m = 1` foi integrado pela PR #222, merge
`e55858690e296d00c88692b8f30902987e853137`. Em seguida, a PR #224 integrou
`c5ZeroExpStage1_eq`, commit de prova
`a908789fad182aa9a2d8eb85b2da641c11c4da62`, merge na `main`
`d667abfc42020e442c62ec1b49b82f5bcf1971ad`. A caixa de estágio 1 coincide com
os extremos exportados, com os quatro pisos/tetos provados exatamente. Build
Lean 4.32 e auditoria isolada passaram; o GitHub não reportou checks. Evidências
e hashes estão em `evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.

`c5ZeroExpStage2_eq` e seus quatro lemas de arredondamento foram integrados
pela PR #226, commit de prova `ab0f2782369e7f0966fa6c769d23ca18ea9abb1f`,
merge `96579150be6700793970bf8cd84f91dd2cccb102`; o GitHub não reportou checks.

Agora `c5ZeroExpStage3_eq` e os oito lemas sobre os extremos e arredondamento
da caixa quadrada do estágio 2 passaram build e auditoria; esta prova importa
o módulo de estágio 2 já integrado. A PR #228 integrou o checkpoint: commit de
prova `682eae99f4b05abd70ee8068aada7bc2af3e0ebb`, merge na `main`
`0d312c654015bf10384969e64f352b0313e2dd39`. O GitHub não reportou checks
hospedados.

Agora `c5ZeroExpStage4_eq` e os oito lemas dos extremos e arredondamentos do
quadrado do estágio 3 passaram build e auditoria em Lean 4.32. A PR #230
integrou o checkpoint: commit de prova
`fe2df2cd361d0d5096d6c4503468833e364b4481`, merge na `main`
`f89cb99d6790bb2c84985c67022b8045a7fb181f`. O GitHub não reportou checks.

Agora `c5ZeroExpStage5_eq` e os oito lemas dos extremos e arredondamentos do
quadrado do estágio 4 passaram build e auditoria em Lean 4.32. A caixa exata
resultante tem parte real `[(2^896 - 23)/2^896, (2^896 + 31)/2^896]` e parte
imaginária `[-31/2^896, 31/2^896]`. O estágio 5 foi integrado pela PR #232:
commit de prova
`821b119d4f0d506e685a585d7f3a52c00a6a95d5`, merge na `main`
`75bacc9c2b7ca8113ee906c61a411922e01bb978`. O GitHub não reportou checks;
pins, hashes e logs estão registrados na evidência do nó trivial.

Agora `c5ZeroExpStage6_eq` e os oito lemas dos extremos e arredondamentos do
quadrado do estágio 5 passaram build e auditoria em Lean 4.32. A caixa exata
resultante tem parte real `[(2^896 - 47)/2^896, (2^896 + 63)/2^896]` e parte
imaginária `[-63/2^896, 63/2^896]`. A PR #234 integrou o estágio 6: commit de
prova `a9be0be89794465fefa44bf66c3b50d5702cc0f5`, merge na `main`
`5571ceb84e0483da55ff7ba212942a4ab13b7cab`. O GitHub não reportou checks;
pins, hashes e logs estão registrados na evidência do nó trivial.

1. **Integrado pela PR #239:** a recorrência exata das caixas para `2 ≤ k ≤ 192`
   foi provada sem criar um certificado separado por estágio. A prova, build,
   auditoria, pins e comandos estão em
   `evidence/rational-boxes/c5-generic-exp-recurrence-20261107/`.
2. Retomar a ponte formal CSV–Lean e avaliar, em etapas, os demais termos da
   caixa; depois compor Gamma, o fator de π e a fonte C2 original e provar as
   inclusões `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.

O trabalho C1B/C2/C3 está integrado (PRs #155/#157/#159). Não reabrir uma
migração geral para Lean 4.35, a lei distância × profundidade ou os novos
cadernos nesta etapa. C5 e os sinais O3 continuam incompletos.

**Estado atual:** a cobertura adaptativa dos 129 nós foi integrada pela PR
#209, commit de prova `05dae531d4ec10c916c340f58255f35977a3abdd`, merge
`386b654eabe4c942d6b0db46754120ab79b52fb5`. C2/C3 da missão de negatividade
estão concluídas: C1B pela PR #155 (merge
`0586e238441096ecd2248e3f14bdac3a832af427`), C2 pela PR #157 (merge
`f4f5cf5ecc60ea3747cbaf21389fab52832d3949`) e C3 pela PR #159 (merge
`b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`). A prioridade ativa é a
certificação finita C5.

**Checkpoint de execução integrado pela PR #211:** commit
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`, merge na `main`
`c6dd548bcb030a21bb90c1aee08023c2ca2d485f`. `c5BernoulliPrimeTable` e a caixa
centrada com tabela compartilhada compilam e passam pela auditoria padrão de axiomas.
Três nós foram avaliados em 2:20 com uma só tabela. A tentativa de lote 129
encerrou após 15:57 sem largura final; a memória ficou em ~6,5 GiB, então o
limite é tempo de CPU. Evidência em
`evidence/rational-boxes/c5-fast-bernoulli-table-validation.md`.

**Exportação de zeta integrada pela PR #213:** commit
`f51db20fa6fd21e08bbc2080cdd4bcb2265e2ea1`, merge na `main`
`5fe8a7b330d6a106e2b2c44781b8d0677c7ea7f3`. Foram exportados 516 caixas
racionais (129 nós em quatro coordenadas); a prova de igualdade entre o CSV
e as definições Lean segue pendente.

**Tentativa local de ponte formal (2026-11-07, não validada):** a primeira
caixa `(a,j)=(2/5,0)` foi testada com `decide`, `rfl` e `norm_num` certificado.
Nenhum método fechou: `decide` não reduz `Rat.num`, `rfl` não é conversível, e
a expansão monolítica excede 1 milhão de passos após ~28 minutos. Não há
`.olean` válido, auditoria aprovada ou inclusão C5. Os erros e o comando estão
preservados em `evidence/rational-boxes/c5-exported-box-proof-attempt/`.
Checkpoint integrado pela PR #215, commit `baa5e3e`, merge na `main`
`6bfb4b14606ec1896a2d01d60be4ca54117bd128`.

**Subcomponente `log 2` testado:** agora está certificado em
`evidence/rational-boxes/c5-log2-component-validation/`: 16 blocos de 32 termos
provam as duas somas racionais de 512 termos e a igualdade exata do intervalo
exportado. Build Lean 4.32.0 com warnings como erros e auditoria fail-closed
das três raízes passaram; só aparecem axiomas padrão. A tentativa direta
anterior e seu histórico permanecem em
`evidence/rational-boxes/c5-log2-component-attempt/` e foram registrados pela
PR #217 (merge `30a615cafa3b27de40427a73cc64988c77e236d3`). A prova em blocos
foi integrada pela PR #219, commit `bd84a673b3c5c1c82168a6655c59ad6a28bbf127`,
merge na `main` `d6ed8ad249ef69c33920164fe43821cc83f138a8`.

1. **Concluído nesta etapa:** exportar os extremos racionais para os quatro
   valores reais e todos os 129 nós; CSV, sondas, logs, pins e reprodução em
   `evidence/rational-boxes/c5-centered-all-a-zeta-export-validation.md`.
2. Continuar a decomposição da caixa piloto nos componentes ainda não
   certificados (cabeça, correções de Bernoulli e exponencial), e provar em
   Lean a ligação formal dos extremos CSV às caixas calculadas. O resultado de
   `log 2` cobre apenas o componente central, não as 516 igualdades. Em seguida,
   escolher `nExp`/`p` para a precisão O3, compor com Gamma, o fator original
   dependente de π e a fonte C2, preservando a cabeça e a cauda exata, e provar
   as inclusões em `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
3. Auditar os teoremas finais de sinal C5 depois das duas inclusões.

Ainda não há inclusão dos coeficientes C2 nas caixas O3, então os sinais C5
continuam condicionais. A validação integrada, com pins, hashes, logs e
comandos, está em `evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`.
A lei quantitativa distância × profundidade e os
novos cadernos ficam para depois; não é necessário calcular a primeira
profundidade de falha para provar a negatividade eventual já concluída em C2.
