# Próximos passos — C5

## Atualização — estágio Taylor 11 integrado pela PR #261

`c5RoundedExpStateC_stage11_correct` passou em Lean 4.32.0 com
`warningAsError=true`; cinco raízes auditadas mostram somente axiomas padrão.
Fonte e registros estão em
A PR #261 integrou o commit de prova
`0240e4cf8fbe192042b6116cd30bee66c2f42594` no merge
`cb271df9a03500440be8e510bffc74a78311252f`; o GitHub não reportou checks
hospedados. O checkpoint cobre apenas `n≤11` no nó `(2/5,0)`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage11-20261107/README.md`.

1. Estender a recorrência para `n=12` e prosseguir até `n=192`.
2. Certificar as quadraturas e a caixa nodal completa.
3. Provar a ponte CSV–Lean, as inclusões da fonte C2 e os sinais finais.

C5 continua incompleta.

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
