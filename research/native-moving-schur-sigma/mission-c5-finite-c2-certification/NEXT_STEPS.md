# Próximos passos — C5

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

1. **Concluído nesta etapa:** exportar os extremos racionais para os quatro
   valores reais e todos os 129 nós; CSV, sondas, logs, pins e reprodução em
   `evidence/rational-boxes/c5-centered-all-a-zeta-export-validation.md`.
2. Importar os extremos exportados como constantes Lean e provar que coincidem
   com as definições das caixas. Depois escolher `nExp`/`p` para a precisão O3
   e compor as caixas com Gamma, o fator original dependente de π e a expressão
   da fonte C2; preservar a cabeça e a cauda exata; provar as inclusões em
   `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
3. Auditar os teoremas finais de sinal C5 depois das duas inclusões.

Ainda não há inclusão dos coeficientes C2 nas caixas O3, então os sinais C5
continuam condicionais. A validação integrada, com pins, hashes, logs e
comandos, está em `evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`.
A lei quantitativa distância × profundidade e os
novos cadernos ficam para depois; não é necessário calcular a primeira
profundidade de falha para provar a negatividade eventual já concluída em C2.
