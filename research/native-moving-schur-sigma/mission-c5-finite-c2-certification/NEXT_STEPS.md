# Próximos passos — C5

**Estado atual:** a cobertura adaptativa dos 129 nós foi integrada pela PR
#209, commit de prova `05dae531d4ec10c916c340f58255f35977a3abdd`, merge
`386b654eabe4c942d6b0db46754120ab79b52fb5`. C2/C3 da missão de negatividade
estão concluídas; a prioridade ativa é a certificação finita C5.

1. Escolher `nExp`/`p` para a precisão O3 e exportar os extremos racionais das
   caixas de zeta nos nós. A cobertura de todos os `j=0,…,128` e a conjugação
   já estão provadas em `c5RationalZetaAdaptiveNodeBox_contains_at` e
   `c5RationalZetaAdaptiveNodeConjugateBox_contains_at`.
2. Compor as caixas com Gamma, o fator original dependente de π e a expressão
   da fonte C2; preservar a cabeça e a cauda exata; provar as inclusões em
   `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
3. Auditar os teoremas finais de sinal C5 depois das duas inclusões.

Ainda não há inclusão dos coeficientes C2 nas caixas O3, então os sinais C5
continuam condicionais. A validação integrada, com pins, hashes, logs e
comandos, está em `evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`.
A lei quantitativa distância × profundidade e os
novos cadernos ficam para depois; não é necessário calcular a primeira
profundidade de falha para provar a negatividade eventual já concluída em C2.
