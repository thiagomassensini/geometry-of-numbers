# Próximos passos — C5

## Prioridade imediata — publicar estágio 6; depois generalizar a recorrência

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
imaginária `[-63/2^896, 63/2^896]`. A publicação do estágio 6 ainda está
pendente; pins, hashes e logs estão registrados na evidência do nó trivial.

1. Publicar e integrar o estágio 6; depois provar a recorrência exata das
   caixas para `2 ≤ k ≤ 192`, sem criar um certificado separado por estágio.
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
