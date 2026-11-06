# Próximos passos — C5

**Estado:** a identidade de Euler–Maclaurin de ordem alta e a cota da cauda
`<10^-250` foram provadas e auditadas localmente em Lean 4.32. O checkpoint é
parcial. C2/C3 da missão de negatividade já estão concluídas; este trabalho
segue na certificação finita C5.

1. Integrar a identidade e a cota como um checkpoint pequeno, com build,
   auditoria, logs, pins e hashes em
   `evidence/rational-boxes/euler-maclaurin-high-order/`.
2. Avaliar por aritmética intervalar racional a parte finita da fórmula em
   `N=100`, `P=300` nos 129 nós; somar a inflação de erro `<10^-250` para a
   cauda inteira. Usar o teorema real no nó `j=0` e a continuação analítica
   para `j>0`.
3. Compor essas caixas com o fator Gamma e a fonte C2 original, preservando a
   definição do coeficiente. Provar as inclusões nas caixas C2 de ambos os
   deslocamentos.
4. Só então concluir os sinais C5 incondicionais e atualizar o estado final.

Continuam adiados a lei quantitativa distância × profundidade e os novos
cadernos. Não é necessário calcular a primeira profundidade de falha para a
negatividade eventual já concluída em C2.
