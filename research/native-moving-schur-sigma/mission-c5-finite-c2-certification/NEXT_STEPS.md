# Próximos passos — C5

**Estado atual:** a PR #208 está integrada em `main` no merge
`296e899e70bee78c54a3278e73e9bd89eaafaa58`. O novo checkpoint da cobertura
adaptativa dos 129 nós compila e passa a auditoria local, mas ainda não foi
publicado. C2/C3 da missão de negatividade estão concluídas; a prioridade
ativa é a certificação finita C5.

1. Publicar pela sequência checkpoint → push → PR → merge a prova adaptativa
   já compilada, seus logs, pins e auditoria. A revisão local está descrita em
   `evidence/rational-boxes/c5-adaptive-zeta-node-instantiation-validation.md`.
2. Escolher `nExp`/`p` para a precisão O3 e exportar os extremos racionais das
   caixas de zeta nos nós. A cobertura de todos os `j=0,…,128` e a conjugação
   já estão provadas em `c5RationalZetaAdaptiveNodeBox_contains_at` e
   `c5RationalZetaAdaptiveNodeConjugateBox_contains_at`.
3. Compor as caixas com Gamma, o fator original dependente de π e a expressão
   da fonte C2; preservar a cabeça e a cauda exata; provar as inclusões em
   `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
4. Auditar os teoremas finais de sinal C5 depois das duas inclusões.

Ainda não há inclusão dos coeficientes C2 nas caixas O3, então os sinais C5
continuam condicionais. A lei quantitativa distância × profundidade e os
novos cadernos ficam para depois; não é necessário calcular a primeira
profundidade de falha para provar a negatividade eventual já concluída em C2.
