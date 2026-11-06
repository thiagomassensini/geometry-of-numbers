# Próximos passos — C5

**Estado:** o checkpoint de Euler–Maclaurin de ordem alta e a cota da cauda
`<10^-250` foram integrados pela PR #205 (merge
`b56a90bceac12248bc5b8e6c2a247849ec885d6e`). C5 permanece parcial. C2/C3 da
missão de negatividade já estão concluídas; este trabalho segue na
certificação finita C5.

1. Avaliar por aritmética intervalar racional a parte finita da fórmula em
   `N=100`, `P=300` nos 129 nós; somar a inflação de erro `<10^-250` para a
   cauda inteira. Usar o teorema real no nó `j=0` e a continuação analítica
   para `j>0`.
2. Compor essas caixas com o fator Gamma e a fonte C2 original, preservando a
   definição do coeficiente. Provar as inclusões nas caixas C2 de ambos os
   deslocamentos.
3. Só então concluir os sinais C5 incondicionais e atualizar o estado final.

Continuam adiados a lei quantitativa distância × profundidade e os novos
cadernos. Não é necessário calcular a primeira profundidade de falha para a
negatividade eventual já concluída em C2.
