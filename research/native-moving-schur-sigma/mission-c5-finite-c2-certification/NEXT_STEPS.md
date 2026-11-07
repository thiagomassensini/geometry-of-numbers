# Próximos passos — C5

## Prioridade imediata — fechar a igualdade do estágio 1 (2026-11-07)

O núcleo `m = 1` já está formalizado e compilado: o log centrado vira a caixa
exata `0`, o argumento do termo de Dirichlet vira `0`, e a exponencial
arredondada preserva a potência nula, a soma unitária e o resto de Taylor
explícito. Os sete teoremas auditados usam somente axiomas padrão. A evidência,
os pins e os comandos estão em
`evidence/rational-boxes/c5-trivial-node-kernel-20261107/`.

Checkpoint parcial integrado pela PR #222, commit de prova
`67e6cf9fdf86ac735b6ade80d2f4a64982968363`, merge na `main`
`e55858690e296d00c88692b8f30902987e853137`; não houve checks hospedados.

1. Resolver os limites inteiros que determinam as extremidades arredondadas
   no estágio 1, compilar e auditar o próximo lema isolado.
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
