# C5 — obrigações abertas

## Estado atual — C5 e reprodução auditadas (2026-11-07)

- `origin/main` está em `d6f8ad760856e6f48a17fb2a7ec5c70e8ffb96db` (após PR #277). Branch de trabalho: `codex/c5-after-pr277-20261107`. PR #277 (`C5: record interval reproductions and active mission state`) integrou o checkpoint e a reprodução em 2026-11-07; sem checks hospedados.
- C1B já entrou pela PR #155, merge `0586e238441096ecd2248e3f14bdac3a832af427`; C2 pela PR #157, merge `f4f5cf5ecc60ea3747cbaf21389fab52832d3949`; C3 pela PR #159, merge `b9cae2c0f4291ba7968c3ded2f2fecedf71cf9e8`. C4 e a recorrência dos momentos também estão integradas. Não reabrir essas fases nem a migração geral para Lean 4.35.
- C5 O2 (`SigmaFiniteCoefficientSignTransport`) está provada em Lean 4.32: recorrência polinomial sem divisão e transporte do sinal para `sigmaPadeD` original. O3 também está provada e auditada, mas **condicionada** às inclusões `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
- Reproduzi as três configurações de `certify_finite_c2.py`; o verificador racional exato confirmou `+++++++++++-`, `+++++++++++-` e `+++++++++-`. Logs, JSONs e hashes: `evidence/rational-boxes/reproduction-20261107/`. A execução precisou do patch local `gmpy2.mpz`→`int`, já preservado em `evidence/interval-certificate/momentos-gmpy2-compat.patch`; o checkout Momentos foi restaurado limpo. Esses resultados continuam condicionais e não provam a inclusão formal da fonte.
- A PR #213 já exportou 516 caixas racionais de zeta nos 129 nós e quatro coordenadas. `#eval`/CSV confirma a exportação e a cobertura, mas ainda não há prova Lean de que cada valor exportado seja igual à caixa usada na composição. A tentativa monolítica para uma caixa está documentada como falha; não a repetir.
- Último resultado formal relevante à avaliação nodal: `c5RationalZetaCenteredNodeBoxWithTable_contains`, em `SigmaC5RationalNodeCenteredInstantiate.lean` (Lean 4.32). O checkpoint auxiliar `c5RoundedExpStateC_stage18_correct` também está integrado, mas não define o próximo passo da missão.
- **Próxima obrigação:** retomar a prova composicional por componentes da caixa zeta exportada (cabeça, correções de Bernoulli e exponencial), reutilizando a igualdade de `log 2` já provada em blocos. Depois ligar Gamma, fator de π e a fonte C2 original, mantendo cabeça e cauda exata, e provar as duas inclusões. Não tentar novamente uma redução monolítica de 28 minutos.
- Alvo final: provar incondicionalmente os sinais de `sigmaPadeD` original em `d=99/2000` e `d=1/10`. A missão permanece incompleta até as inclusões da fonte e a composição final passarem build e auditoria.


## Checkpoint auxiliar — recorrência de um nó até n=18 integrada pela PR #275

`c5RoundedExpStateC_stage18_correct` compilou e passou pela auditoria em Lean
4.32.0. A PR #275 integrou o commit `eb7209321914de6733de0bd160e1c64633924dba` no merge `df23788957cb17b16832d5f4c9e47fd8aa12d68f`; o GitHub não
reportou checks hospedados. Evidências em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage18-20261107/`. O resultado
cobre somente `n≤18` no nó `(2/5,0)`.

Continuam abertas a extensão até `n=192`, os demais nós, quadraturas, caixa
nodal completa, ponte CSV–Lean, composição com a fonte original e inclusões
`sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. C5 segue parcial; próximo:
`n=19`.

## Checkpoint anterior — recorrência até n=17 integrada pela PR #273

A prova foi integrada pelo merge `41164de6cf0042594833bae02cdab2ce4cd11aae`; cobre somente o nó `(2/5,0)` até
`n=17`. A extensão corrente e os demais itens seguem incompletos.

## Checkpoint anterior — recorrência até n=16 integrada pela PR #271

A prova foi integrada pelo merge `795caa0eebfaa61874c1fff22c683fb85bdf941a`; cobre somente o nó `(2/5,0)` até
`n=16`. A extensão corrente e os demais itens seguem incompletos.

## Checkpoint anterior — recorrência até n=15 integrada pela PR #269

A prova foi integrada pelo merge `fe6d5c238ba9ee796dc5ef56880aa60e89899c63`; cobre somente o nó `(2/5,0)` até
`n=15`. A extensão corrente e os demais itens seguem incompletos.

## Checkpoint anterior — recorrência até n=14 integrada pela PR #267

A prova foi integrada pelo merge `b1a7c9b14eb1352cc470508fdb2bf9a8baaea56a`; cobre somente o nó `(2/5,0)` até
`n=14`. A extensão corrente e os demais itens seguem incompletos.

## Checkpoint anterior — recorrência até n=13 integrada pela PR #265

A prova foi integrada pelo merge `52c57108c74cb5f7f12bdbd94ca616f3bba8cf2a`; cobre somente o nó `(2/5,0)` até
`n=13`. A extensão corrente e os demais itens seguem incompletos.

## Checkpoint anterior — recorrência até n=12 integrada pela PR #263

A etapa `c5RoundedExpStateC_stage12_correct` está integrada na `main` pelo
merge `4b5b6a0aebd54798e6a26b2eda69994589c78668`. Continua sendo apenas um nó
até `n=12`; a extensão corrente para `n=13` e os demais itens desta lista
seguem incompletos.

## Atualização — recorrência de um nó até n=10 integrada pela PR #259

`c5RoundedExpStateC_stage10_correct` compilou e passou pela auditoria em Lean
4.32.0. Evidências em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage10-20261107/`. A PR #259
integrou o commit de prova `5dd4f4874a192e83af26640f412f81f42239487b` no
merge `d68eec91118e2cdcb89fced66a14062ef6170cf9`; não houve checks hospedados.
O resultado cobre somente `n≤10` no nó `(2/5,0)`.

Continuam abertas a extensão até `n=192`, os outros nós, quadraturas, caixa
nodal completa, ponte CSV–Lean, composição com a fonte original e inclusões
`sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. C5 segue parcial; próximo:
`n=11`.

## Atualização — recorrência de um nó até n=9 integrada pela PR #257

`c5RoundedExpStateC_stage9_correct` compilou e passou pela auditoria de axiomas
em Lean 4.32.0. Evidências em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage9-20261107/`. A PR #257
integrou o commit de prova `62c9fbd7b04034f21ccf0336abf0d83d8c6a6592` no
merge `9655308b17dbf565d272f7578545bb68b7b0b867`; não houve checks hospedados.
A prova cobre somente `n≤9` no nó `(2/5,0)`.

Continuam abertas a extensão até `n=192`, os outros nós, as quadraturas, a
caixa nodal completa, a ponte CSV–Lean, a composição com a fonte original e as
inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. C5 segue parcial; o
próximo estado é `n=10`.

## Atualização — recorrência de um nó até n=8 integrada pela PR #255

`c5RoundedExpStateC_stage8_correct` compilou e passou pela auditoria em Lean
4.32.0. Fonte e registros estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage8-20261107/`. A PR #255
integrou o commit de prova `96f5f5709829282756bc8c8a2b52a80290c96735` no
merge `29d363068d52c62c37afc3896f6b3d46f734f16b`; não houve checks hospedados.
A prova cobre somente `n≤8` no nó `(2/5,0)`.

Continuam abertas a recorrência até `n=192`, os outros nós, as quadraturas, a
caixa nodal completa, a ponte CSV–Lean, a composição com a fonte original e as
inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. C5 segue parcial; o
próximo estado é `n=9`.

## Atualização — recorrência de um nó até n=7 integrada pela PR #253

`c5RoundedExpStateC_stage7_correct` compilou e passou pela auditoria de axiomas
em Lean 4.32.0. Fonte, logs e hashes estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage7-20261107/`. A PR #253
integrou o commit de prova `a08a5c9c5a1d02fc33b3207ef2be3d362d526de8` no
merge `952fcd76093681f3feacc540bb0db9c49bfc6034`; não houve checks hospedados.
O escopo é somente `n≤7` no nó `(2/5,0)`.

Continuam abertas a recorrência até `n=192`, os demais nós, as quadraturas, a
caixa nodal completa, a ponte CSV–Lean, a composição com a fonte original e as
inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. C5 segue parcial. O
próximo estado a provar é `n=8`.

## Atualização — recorrência de um nó até n=6 integrada pela PR #251

`c5RoundedExpStateC_stage6_correct` foi compilado e auditado em Lean 4.32.0,
com apenas axiomas padrão. A fonte e os logs estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage6-20261107/`. A PR #251
integrou o commit de prova `e6c9ef307c69c59a8e665232b4b0271c481d8fcd` no
merge `7b61a5ceb0d8567c33fe27a5810d493f4640ed69`; não houve checks hospedados.
Ele cobre somente `n≤6` para `(2/5,0)`.

Continuam abertas a extensão até `n=192`, os demais nós, as quadraturas, a
caixa nodal completa, a ponte CSV–Lean, a composição das caixas com a fonte
original e as inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. C5
segue parcial. O próximo passo é provar `n=7`.

## Atualização — recorrência de um nó até n=5 integrada pela PR #249

A recorrência `c5RoundedExpStateC` foi provada até `n=5` no nó `(2/5,0)`.
Faltam os estados restantes até `n=192`, as quadraturas e a caixa nodal
completa; em seguida, a ponte CSV–Lean, a composição da fonte e as inclusões
`sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage5-20261107/README.md`.
A PR #249 integrou o checkpoint, commit de prova `1782048f05c43fc31e491fa7192105235b34a14e`, merge
`58b9a61532f79f6aa51ebfb48edaacf728be3738`; o GitHub não reportou checks.
C5 continua parcial.


## Atualização — estado de um nó até n=4 integrado pela PR #247

A recorrência foi formalizada até `n=4` para `(a,j)=(2/5,0)` e integrada pela
PR #247, merge `ab6d5f1923770d4db830ba9ebf2fbc17c9626149`; o GitHub não reportou
checks. A extensão até `n=192` e a avaliação nodal completa continuam abertas.
Faltam também as quadraturas, a ponte CSV–Lean, a composição da fonte e as
inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage4-20261107/README.md`; C5
segue parcial.


## Atualização — recorrência de um nó até n=3 integrada pela PR #245

A transição para o estado `n=3` foi provada para `(a,j)=(2/5,0)` e integrada
pela PR #245, merge `727b3920d12e0979c5f722a04732fb346fc880d8`; o GitHub não
reportou checks. Ainda faltam `n=4…192`, as quadraturas da exponencial
e a igualdade com o termo nodal completo; depois, a ligação das caixas à fonte
C2 e as inclusões `sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes`. Evidência em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage3-20261107/README.md`.
Este piloto não fecha a validação C5.


## Atualização — estado parcial do termo nodal m=2

O piloto `(a,j)=(2/5,0)` agora prova, em Lean 4.32, somente a recorrência
`c5RoundedExpStateC` até `n=2`. Permanecem em aberto `n=3…192`, as quatro
quadraturas da exponencial, a igualdade com o termo nodal completo e a inclusão
desse nó na composição dos coeficientes C2. A exportação `#eval` de todos os
estados não é certificado formal. O checkpoint local foi integrado pela PR #243, merge
`20c30cec4b3964fc063d8eb3c93e09a41d319cfc`; os checks hospedados não foram
reportados. Evidência, comandos e erros estão em
`evidence/rational-boxes/c5-m2-dirichlet-term-stage2-20261107/README.md`.
As inclusões `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes` e os sinais finais
C5 continuam abertos.


## Atualização — recorrência genérica integrada pela PR #239 (2026-11-07)

`c5RoundedExpC_zero_stage_2_to_192_closed_form` formaliza os estágios 2–192
na entrada zero com os parâmetros `3*2^(k-2)-1` e `4*2^(k-2)-1`, mantendo a
definição original e seu resto. O build Lean 4.32.0 com `warningAsError=true`
e a auditoria isolada passaram com axiomas padrão. A evidência está em
`evidence/rational-boxes/c5-generic-exp-recurrence-20261107/`. O commit de prova
`be04221f5eb4a174804fb96c9011d0b58bfc2642` foi integrado pela PR #239 no merge
`8c3691e59f9280864b93c4868eb465dbdad6da2c`; não houve checks hospedados.

Continuam abertas a ligação formal das 516 caixas CSV às definições Lean, a
composição completa da fonte C2, as inclusões
`sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes` e os sinais finais C5. Não
reiniciar C1B, C2 ou C3.

## Nota de validação numérica — replay de 2026-11-07

As caixas experimentais da primeira janela negativa foram reproduzidas usando
uma cópia local do avaliador Momentos com conversões `gmpy2.mpz` → `int`. O
checker racional independente repetiu os sinais condicionais. A tentativa sem
patch e seus logs também foram preservados. Isso não prova a inclusão das
saídas de `mpmath.iv` nas caixas. A recorrência genérica da exponencial
arredondada foi integrada pela PR #239; a ponte CSV–Lean, a composição da fonte
C2 e as inclusões
`sigmaC00495SourceBoxes`/`sigmaC01SourceBoxes` continuam abertas. Registro
reproduzível:
`evidence/interval-certificate/reproduction-2026-11-07.md`.
O checkpoint foi integrado pela PR #237 no merge
`5fe7837e0f9509950aeb95777bdd220d68835ad8`; o GitHub não reportou checks
hospedados.

## Atualização — estágio 6 integrado; composição da fonte ainda aberta

Os lemas `c5CenteredLogQFromLogTwo_one`,
`c5CenteredDirichletExponentArg_one`,
`c5CenteredDirichletTermBoxWithLogTwo_one`,
`c5RoundedExpStateC_zero_succ` e `c5RoundedExpSmall_zero`, junto aos lemas de
estado/log usados por eles, compilam em Lean 4.32.0 e passaram por auditoria
de axiomas: somente `propext`, `Classical.choice` e `Quot.sound`.
`c5RoundedExpSmall_zero` conserva o resto racional, sem hipótese de sinal.

`c5ZeroExpStage1_eq` prova que a exponencial arredondada do estágio 1 com
argumento zero é a caixa exportada. Os quatro pisos e tetos foram reduzidos a
desigualdades racionais exatas e auditados em Lean 4.32; o relatório contém o
build de prova e a auditoria por import. A tentativa antiga, que aplicava os
lemas de piso/teto à igualdade composta, continua guardada somente como
histórico. A evidência está em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.
O resultado foi integrado pela PR #224, commit de prova
`a908789fad182aa9a2d8eb85b2da641c11c4da62`, merge
`d667abfc42020e442c62ec1b49b82f5bcf1971ad`; não houve checks hospedados.

`c5ZeroExpStage2_eq` e os quatro lemas de arredondamento da caixa quadrada do
estágio 1 também foram provados, compilados e auditados. Esse checkpoint foi
integrado pela PR #226, commit de prova
`ab0f2782369e7f0966fa6c769d23ca18ea9abb1f`, merge
`96579150be6700793970bf8cd84f91dd2cccb102`; não houve checks hospedados.
Continuam abertas a ligação do CSV, a composição completa da fonte e as
inclusões O3.

`c5ZeroExpStage3_eq`, com oito lemas para a expressão exata da caixa quadrada
do estágio 2 e seus pisos/tetos, foi compilado, auditado e integrado em módulo
separado que importa o estágio 2 integrado. O estágio 3 foi integrado pela
PR #228, commit de prova
`682eae99f4b05abd70ee8068aada7bc2af3e0ebb`, merge na `main`
`0d312c654015bf10384969e64f352b0313e2dd39`; o GitHub não reportou checks
hospedados. A ponte CSV–Lean, a composição completa da fonte e as inclusões O3
seguem abertas.

`c5ZeroExpStage4_eq`, com oito lemas para os extremos exatos do quadrado do
estágio 3 e seus pisos/tetos, foi compilado e auditado em módulo separado que
importa o estágio 3 integrado. O estágio 4 foi integrado pela PR #230, commit
de prova `fe2df2cd361d0d5096d6c4503468833e364b4481`, merge na `main`
`f89cb99d6790bb2c84985c67022b8045a7fb181f`; o GitHub não reportou checks.
O estágio 4 foi integrado. A ponte CSV–Lean, a composição completa da fonte e
as inclusões O3 seguem abertas.

`c5ZeroExpStage5_eq`, com oito lemas para os extremos exatos do quadrado do
estágio 4 e seus pisos/tetos, foi compilado e auditado em módulo separado que
importa o estágio 4 integrado. A caixa exportada é
`[(2^896 - 23)/2^896, (2^896 + 31)/2^896] × [-31/2^896, 31/2^896]`.
O estágio 5 foi integrado pela PR #232, commit de prova
`821b119d4f0d506e685a585d7f3a52c00a6a95d5`, merge na `main`
`75bacc9c2b7ca8113ee906c61a411922e01bb978`; o GitHub não reportou checks.
O estágio 5 está integrado. A ponte CSV–Lean, a composição completa da fonte e
as inclusões O3 seguem abertas.

`c5ZeroExpStage6_eq`, com oito lemas para os extremos exatos do quadrado do
estágio 5 e seus pisos/tetos, foi compilado e auditado em módulo separado que
importa o estágio 5 integrado. A caixa exportada é
`[(2^896 - 47)/2^896, (2^896 + 63)/2^896] × [-63/2^896, 63/2^896]`.
O estágio 6 foi integrado pela PR #234, commit de prova
`a9be0be89794465fefa44bf66c3b50d5702cc0f5`, merge na `main`
`5571ceb84e0483da55ff7ba212942a4ab13b7cab`; o GitHub não reportou checks.
O subpasso de generalização da recorrência foi integrado pela PR #239. A ponte
CSV–Lean, a composição completa da fonte e as inclusões O3 seguem abertas.

Continuam abertas a ligação formal das 516 linhas CSV às caixas Lean, a
composição de todos os termos da fonte C2 original, as inclusões
`sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes` e os sinais finais C5. O
checkpoint parcial do nó trivial foi integrado pela PR #222, commit de prova
`67e6cf9fdf86ac735b6ade80d2f4a64982968363`, merge na `main`
`e55858690e296d00c88692b8f30902987e853137`; ele não fecha C5.

## Atualização — componente `log 2` fechado; composição C5 continua aberta

`SigmaC5Log2Certified.lean` certifica as duas somas de 512 termos em 16 blocos
racionais de 32 termos e prova a igualdade exata do intervalo exportado.
Compilação Lean 4.32.0 e auditoria fail-closed passaram, apenas com os axiomas
padrão. Os detalhes, hashes, pins, logs e comando estão em
`evidence/rational-boxes/c5-log2-component-validation/README.md`.
O checkpoint foi integrado pela PR #219, commit
`bd84a673b3c5c1c82168a6655c59ad6a28bbf127`, merge na `main`
`d6ed8ad249ef69c33920164fe43821cc83f138a8`.

Isso não certifica os extremos das 516 linhas CSV contra as caixas Lean, nem
avalia os componentes restantes ou prova as inclusões
`sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. C5 e os sinais finais continuam
abertos. A tentativa piloto CSV–Lean permanece o primeiro erro concreto: a
redução `decide` para em `Rat.num`, `rfl` não é conversível e `norm_num` excedeu
1 milhão de passos após ~28 minutos. O próximo passo é fatorar os componentes
restantes e estabelecer a ponte formal em um caso piloto.

## Snapshot mais recente — cobertura zeta adaptativa provada, composição C5 aberta

`SigmaC5RationalNodeLogBounds.lean` e `SigmaC5RationalNodeInstantiate.lean`
instanciam as condições adaptativas de log/exp e provam a inclusão de zeta nos
129 nós `b=j/100000`, `0≤j≤128`, para `a∈[2/5,3/5]`, bem como nos argumentos
conjugados. A escala prova `m/2^k∈[1/2,1]`; os limites uniformes de `logQ`
ficam em `[-5,5]`, e a potência tem `normBound≤4`. A cauda exata continua
incluída com inflação `<10^-250`.

O build limpo Lean 4.32 e o checker fail-closed de 21 raízes passaram, apenas
com axiomas padrão. O checkpoint foi integrado pela PR #209, commit de prova
`05dae531d4ec10c916c340f58255f35977a3abdd`, merge
`386b654eabe4c942d6b0db46754120ab79b52fb5`; evidência reproduzível em
`evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`.

**Ainda faltam** ligar formalmente os extremos racionais exportados às caixas
Lean, compor com Gamma, o fator de π e a expressão da fonte C2, e provar as
inclusões em `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`. Portanto, os
sinais O3 continuam condicionais e C5 não está concluída. Próximo passo:
formalizar uma caixa piloto, compor a fonte original mantendo sua cabeça e
cauda exata e provar as duas inclusões.

## Tentativa piloto CSV–Lean ainda aberta (2026-11-07)

Os 516 extremos racionais em `c5-centered-all-a-zeta-boxes.csv` vieram de
sondas `#eval`; ainda não há igualdade Lean que os ligue a
`c5RationalZetaCenteredNodeBox`. A prova piloto de uma linha não fechou com
`decide`, `rfl` ou `norm_num` expandido. Não usar esses extremos como fatos
formais. O subpasso `c5CenteredLog2I 512`, antes pendente, foi concluído pela
prova em blocos registrada acima; ela cobre apenas o componente `log 2`.
Evidência e erros do piloto CSV–Lean:
`evidence/rational-boxes/c5-exported-box-proof-attempt/`; a prova isolada de
`log 2` está em `evidence/rational-boxes/c5-log2-component-attempt/`. O diagnóstico inicial foi publicado pela PR #215, merge
`6bfb4b14606ec1896a2d01d60be4ca54117bd128`; o teste isolado de `log 2` e
seus limites foram integrados pela PR #217, merge
`30a615cafa3b27de40427a73cc64988c77e236d3`.

As inclusões `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes` seguem abertas,
bem como composição C5; os sinais permanecem condicionais. C5 não está
concluída.

## Checkpoint anterior — ponte Gamma genérica integrada pela PR #198

A ponte integrada pela PR #198, `SigmaC5GammaRationalCore.lean`, separa `gammaFinite` em um
fator `T^z` certificado por `dirichletTermBox2` e um núcleo em `ℚ+iℚ` exato;
`gamma3072Interval_contains` transporta o erro Gamma `10^-259` já provado para
um retângulo da Gamma verdadeira. Build Lean 4.32 e auditoria de seis raízes
passaram, só com axiomas padrão. Ela não fornece ainda extremos efetivos para
os argumentos dos nós `w±`, nem limites da potência e tampouco caixa para
`riemannZeta w±`. A fonte C2 e a genealogia cabeça+cauda continuam preservadas;
as caixas O3 permanecem condicionais e C5 não está completa.

Próxima obrigação matemática: obter e formalizar um resto Euler–Maclaurin/
Hurwitz de ordem alta adequado ao domínio de `w±`, depois compor as avaliações
de Gamma, zeta, fator de π e demais termos da expressão C2 original em cada nó.
Detalhes do subpasso Gamma em `evidence/rational-boxes/c5-gamma-rational-core-validation.md`.

As três gerações experimentais dos coeficientes foram reproduzidas numa cópia
temporária do checkout Momentos, e as saídas passaram o verificador exato de
frações: `+++++++++++-` em `d=99/2000` (duas configurações) e `+++++++++-` em
`d=1/10`. Isso valida a propagação racional **dadas as caixas**, mas não prova
que os coeficientes da fonte C2 pertençam a elas. O patch de compatibilidade,
as saídas e os logs estão em `evidence/interval-certificate/`; o registro
detalhado é `reproduction-2026-11-06.md`.

## Snapshot atual — após a cota analítica explícita

Os pesos escalados `0..14` seguem provados e integrados, e a fonte original
tem uma cota uniforme compilada, auditada e integrada pela PR #192:
`CarrySigmaObstruction.displacedProductC_norm_le_10pow13_on_ball_39`
estabelece `‖displacedProductC d z‖≤10^13` para `|d|≤1/10` e
`|z|<39/100`. O domínio de analiticidade aberto de raio `2/5` permanece o
resultado integrado pela PR #189. A interpolação usa contorno exterior
`38/100`, cujo disco fechado está dentro da bola aberta onde a cota Lean vale.
A análise racional exata com esse raio ainda dá erro de interpolação
`<10^-501`, e a amplificação do erro Gamma `10^-259` permanece `<10^-135`.
Veja `evidence/rational-boxes/analytic-bounds-10pow13-validation.md` e
`rational-interpolation-analysis-10pow13-radius-38.log`. A cota `10^100` da
PR #191 segue como wrapper compatível.

Também está integrada pela PR #193 a faixa racional exata de `Real.pi`
construída com a série alternada de `arctan` e a identidade de Machin; detalhes
e logs em `evidence/rational-boxes/c5-pi-bounds-validation.md`. O módulo
fornece uma faixa exata em vez de uma desigualdade decimal simplificada.

Pela PR #195, `SigmaC5PiInterval.lean` certifica `log π`, e
`SigmaC5PiExp.lean` certifica o exponencial correspondente da completação
original para uma caixa complexa de entrada. Commit de prova `321ae94`, merge
`0032b10295bfeaadb29d0387f9b99dde9b160ac3`. A evidência está em
`evidence/rational-boxes/c5-pi-completion-factor-validation.md`.

O4 continua aberta: ainda faltam avaliações certificadas da fonte original
nos 129 nós e a prova de inclusão dos coeficientes C2 originais nas caixas O3.
Os sinais O3 permanecem condicionais e C5 não está concluída. Este snapshot
substitui a afirmação anterior de que a cota analítica ainda faltava; as
seções seguintes preservam o histórico dos checkpoints anteriores.

**Primeiro gargalo numérico localizado:** a rota exata pode reescrever o
escalar nativo como `riemannZeta` no `genuineCriticalStrip`, mas o resultado
Euler–Maclaurin encontrado na revisão pinada é apenas
`HardyFirstZero.zeta_em4_error`, com resto de ordem 4. Em `N=100`, o limite
uniforme de contorno é cerca de `1.351·10⁻⁸`, insuficiente para as caixas O3.
Falta formalizar um resto de ordem alta para zeta/Hurwitz e avaliá-lo por
intervalos Lean; o avaliador Python de ordem 80 não fornece essa prova. Também
falta avaliar em caixas formais a soma de `gammaFinite 3072 620`, embora seu
erro analítico `10⁻²⁵⁹` já esteja provado. Registro reproduzível em
`evidence/rational-boxes/c5-original-source-zeta-route-audit.md`.

## Snapshot histórico — após a validação local dos pesos 2–14

Os pesos escalados de todos os graus `0..14` estão provados em Lean: grau zero
`=1`, grau um `<10^11`, e cada grau `2..14` `<10^145`. A nova prova passou
build limpo e auditoria fail-closed de 23 raízes. A PR #187 integrou esse
incremento: commit `6424f4334edd5c776997116403043635fa0c8f83`, merge
`9f4a1b43cb2b155dfc55bf49ef77d1914210b796`. Veja
`evidence/rational-boxes/degree2-14-weight-bound-validation.md`.

O4 continua aberta: o domínio analítico da fonte deslocada no disco de raio
`2/5` já foi provado e integrado pela PR #189 em `SigmaC5SourceAnalytic.lean`, mas falta uma
cota numérica para o módulo, a avaliação certificada nos 129 nós e a inclusão dos coeficientes
originais nas caixas O3. Portanto, os sinais O3 continuam condicionais, e a
missão C5 não está concluída. As referências históricas abaixo que diziam que
os pesos `2..14` estavam pendentes registram o estado na data dos checkpoints
anteriores; este snapshot atual e
`evidence/rational-boxes/degree2-14-weight-bound-validation.md` as supersedem.

## O1 — validar o cálculo racional publicado — REPRODUZIDO

Os dois verificadores exatos passaram sobre as caixas JSON rastreadas, com resultados `+++++++++++-` e `+++++++++-`. As três configurações de geração intervalar também foram reproduzidas após conversão local de `gmpy2.mpz` para inteiro Python nativo. Logs e patch estão em `evidence/interval-certificate/`.

Isso confirma a implicação racional condicional às caixas; não confirma que os coeficientes verdadeiros estejam nelas.

## O2 — transporte C4 em Lean — PROVADO E AUDITADO

`SigmaFiniteCoefficientSignTransport.lean` prova a recorrência polinomial sem divisão para `pₙ=c₀^(n+1)Hₙ`, com `Hₙ=2*completedSigmaLogJet d n`, a identidade do determinante original e os dois transportes de sinal. Compila em Lean 4.32; `#print axioms` lista somente `propext`, `Classical.choice`, `Quot.sound`.

## O3 — aritmética intervalar racional formal — PROVADO CONDICIONALMENTE E AUDITADO

Os módulos `SigmaFiniteRationalIntervals`, `SigmaFiniteRationalIntervalBoxes`,
`SigmaFiniteRationalIntervalTransport`, `SigmaFiniteRationalIntervalSigns` e
`SigmaFiniteRationalIntervalCertificates` portam as caixas JSON a bolas racionais
exatas, propagam a recorrência original escalada e certificam cada menor no Lean.
Em `d=99/2000`, provam `0 < D_s` para todo `s<11` e `D_11<0`; em `d=1/10`,
provam `0 < D_s` para todo `s<9` e `D_9<0`, sob as hipóteses explícitas de que
os coeficientes verdadeiros pertencem às respectivas caixas (`sigmaC00495SourceBoxes`
e `sigmaC01SourceBoxes`). A composição termina no `sigmaPadeD` original.

Build Lean 4.32 limpo, com warnings como erros, e auditoria transitiva de 13
raízes passaram. Os únicos axiomas são `propext`, `Classical.choice` e
`Quot.sound`. A etapa foi integrada pela PR #167, merge
`fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`. Comandos, logs, hashes de
fontes/oleans e verificador fail-closed estão em `evidence/rational-boxes/`.

## O4 — origem das caixas — ABERTO

Provar inclusões rigorosas dos coeficientes `c₀..c₁₄` em `d=99/2000` e `c₀..c₁₂` em `d=1/10`, preservando cabeça C2 + cauda geométrica exata + completação original. O domínio analítico no disco de raio `2/5` está provado; ainda faltam uma cota numérica explícita do módulo, a avaliação racional estreita da expressão Gamma finita, a cauda Hurwitz/Euler–Maclaurin e a composição nodal/Cauchy, com todos os domínios usados. A saída Python atual não fecha essa obrigação.

O avaliador foi conferido estruturalmente e as três reproduções passaram, mas
`mpmath.iv`/seu backend e as operações complexas elementares ainda não têm prova
Lean de arredondamento externo. Esse é o primeiro bloqueio concreto à
certificação incondicional: sem provar a inclusão da fonte nas caixas, as
conclusões O3 permanecem condicionais.

Uma busca adicional encontrou e recompilou a infraestrutura formal
`ZetaLean.Rigor`, `ZetaLean.IntervalExp` e `ZetaLean.IntervalCExp`, que já
certifica aritmética retangular racional, `log` real, `exp` real/complexo e
`m^{-s}`. A auditoria de quatro raízes retornou somente axiomas padrão; os logs
estão em `evidence/rational-boxes/reused-interval-audit.log`.

**Ponte Euler-Gamma de alta precisão integrada pela PR #173:** `SigmaGammaEulerIntegral.lean`
prova que, para `1495/20000 ≤ Re(z) ≤ 1`, a Gamma original fica a distância no
máximo `10⁻⁹⁹` da expressão finita `gammaFinite 1024 240 z`. O erro Taylor do
trecho compacto é `≤10⁻¹²⁰` e a cauda é `≤exp(-240)≤10⁻¹⁰⁰`. O build Lean 4.32
e a auditoria de dez raízes passaram, com apenas `propext`, `Classical.choice`
e `Quot.sound`. Merge: `72586b6223579ee1b37a6077ad6f2a0eceaf919c`.

**Primeiro subproblema analítico ainda em aberto:** produzir caixas racionais
estreitas para `gammaFinite 3072 620 z` nos pontos racionais de interpolação. A soma
direta tem cancelamento grande; a próxima etapa deve calcular os coeficientes
Taylor racionais da expressão finita antes de aplicar a aritmética intervalar e
certificar o resto da expansão. A identidade formal
`Zeta23.DigammaSeries.inv_gamma_eq_prod` continua sendo uma alternativa. Depois
será preciso compor Hurwitz e Cauchy/Fourier com a ponte C2 exata. Não há prova
de `sigmaC00495SourceBoxes` nem de `sigmaC01SourceBoxes` nesta etapa.

**Ponte Gamma de interpolação, integrada pela PR #175:**
`gamma_finite_3072_620_error` melhora o erro absoluto para `10⁻²⁵⁹` e tem build
Lean 4.32/auditoria de doze raízes. Merge `992ab31c3aacdf3b95b3c02fe58f5f3d529c0cec`.
Uma exploração exata racional sugere evitar a quadratura trigonométrica:
interpolar a densidade par em 129 pontos racionais `t_j=j/100000`. O novo módulo
`SigmaRationalInterpolation.lean` prova que nós distintos recuperam exatamente
qualquer polinômio racional de grau menor que 129 e formaliza a identidade dos
coeficientes com as somas ponderadas de Lagrange. Isso é somente o passo
algébrico. `c5InterpolationWeightSum_zero_eq_one` prova que o peso escalado de
grau zero soma exatamente `1`. Depois, a forma derivativa de grau um permitiu
provar `c5LagrangeBasisProductCoeffOne_bound`,
`c5InterpolationCoeffOneAbsSum_le_six` e
`c5InterpolationWeightSum_one_lt_ten_eleven`. O build limpo e a auditoria
estão em `evidence/rational-boxes/degree1-weight-bound-validation.md`.
Na data deste registro, os limites Lean dos graus `2..14` ainda estavam
pendentes. Eles foram fechados pelo checkpoint local posterior; veja o snapshot
atual no início e `degree2-14-weight-bound-validation.md`. A tentativa anterior
por expansão direta atingiu o limite de passos de `simp`; o erro permanece em
`evidence/rational-boxes/interpolation-weight-degree1-prototype.log`.
Também seguem pendentes a cota analítica
`|completedSigmaDensity d t|≤10^100` no disco de raio `2/5` e a avaliação
rigorosa da fonte nos pontos. A análise exploratória está em
`analyze_rational_interpolation.py` e
`evidence/rational-boxes/rational-interpolation-analysis.log`; build e auditoria
da identidade algébrica estão em `evidence/rational-boxes/VALIDATION.md`.

## O5 — composição, build, axiomas e publicação — PARCIAL

A Fase 1 foi integrada pela PR #165, merge `75691edf0e74cc643f098213f60b684476132175`;
O3 foi integrada pela PR #167, merge `fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`.
O lema algébrico dos 129 nós foi integrado pela PR #177, merge
`0702371cff0c6016eae9eaa0aa9331ae95483456`. O4, a inclusão das caixas e os
teoremas finais incondicionais seguem abertos. O checkpoint de estado pós-PR
#177 foi integrado pela PR #178, merge `7ad7e29195790eedda01645e71e5c52edf1b4e6b`.
A soma exata do peso escalado de grau zero foi integrada pela PR #179, merge
`f6a2298b92cbfddad77abe512d73387efea4e870`; naquele checkpoint, os graus
positivos e O4 permaneciam abertos. O estado pós-PR #179 foi registrado pela PR #180, merge
`de95637d38d5e6d5488342cd5141b88233be6eb7`. A estrutura derivativa de grau um
foi integrada pela PR #181, merge
`7460497307e7ed0ffb47ef1ac96b096e9b410472`. O limite escalado de grau um foi
integrado pela PR #185, merge
`c840ba35711ac8f938fa24c191f2af60f505480d`, com build limpo e auditoria de 21
raízes. A PR #187 integrou os limites dos graus `2..14`, com build limpo e
auditoria de 23 raízes; merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
As demais obrigações O4 continuam abertas.
O estado pós-PR #181 foi registrado pela PR #182, merge
`8f8b9da2b8c1e8f3b8d1290608c8b2abffe9c285`.

## Classificação honesta se O4 continuar em aberto

Manter os resultados que dependem das caixas explicitamente condicionais e relatar precisamente qual coeficiente ou camada de funções elementares bloqueia a inclusão. Não declarar `PROVADO — CERTIFICAÇÃO COMPLETA`.

## Limite dos pesos de grau um — validado localmente

Em 2026-11-06, a prova simbólica baseada em produtos fatoriais passou um build
limpo de `SigmaRationalInterpolation.lean` em Lean 4.32 e uma auditoria
fail-closed de 21 raízes. A auditoria inclui
`c5LagrangeBasisProductCoeffOne_bound`,
`c5InterpolationCoeffOneAbsSum_le_six` e
`c5InterpolationWeightSum_one_lt_ten_eleven`, todos com apenas
`propext`, `Classical.choice` e `Quot.sound`. Evidência e hashes:
`evidence/rational-boxes/degree1-weight-bound-validation.md`.

Naquele checkpoint, o limite de grau um estava publicado e cobria somente esse
grau. Os pesos de graus `2..14` foram integrados depois pela PR #187; a cota
analítica da fonte e as inclusões das caixas continuam abertas.
Os logs das falhas anteriores em
`evidence/rational-boxes/degree1-retry-checkpoint.md` foram mantidos como
histórico de proveniência.
