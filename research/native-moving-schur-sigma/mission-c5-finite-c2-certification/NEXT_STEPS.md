# Próximos passos — C5

**Estado:** o checkpoint de Euler–Maclaurin de ordem alta e a cota da cauda
`<10^-250` foram integrados pela PR #205 (merge
`b56a90bceac12248bc5b8e6c2a247849ec885d6e`). C5 permanece parcial. C2/C3 da
missão de negatividade já estão concluídas; este trabalho segue na
certificação finita C5.

1. `SigmaC5RationalNodeEval.lean` agora fatoriza exatamente a parte de
   Bernoulli de `emZetaHighRHS 100 300` e prova uma caixa genérica para zeta,
   sob condições explícitas. Instanciar `hhead` e `hbase` para os valores
   `b=j/100000`, `0≤j≤128`, e as partes reais dos dois deslocamentos C2;
   tratar as partes imaginárias negativas por conjugação, calcular os
   retângulos racionais concretos e absorver a cauda `<10^-250`.
2. Compor as caixas nodais com Gamma, o fator original dependente de π e a
   fonte C2 original. Preservar a cabeça C2 mais a cauda exata e provar as
   inclusões em `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.
3. Só depois concluir os sinais C5 incondicionais e atualizar o estado final.

O avaliador genérico e a auditoria local estão documentados em
`evidence/rational-boxes/c5-rational-node-evaluator-validation.md`; ainda não
há nenhum nó instanciado nem inclusão de coeficientes provada.

Continuam adiados a lei quantitativa distância × profundidade e os novos
cadernos. Não é necessário calcular a primeira profundidade de falha para a
negatividade eventual já concluída em C2.
