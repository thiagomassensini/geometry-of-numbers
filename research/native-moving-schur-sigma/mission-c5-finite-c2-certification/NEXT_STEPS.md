# Próximos passos — C5

**Estado:** a PR #207 integrou o avaliador racional genérico de zeta e levou
a `main` ao merge `27a61e6bebcce178b81b961f507400ed77b96d3b`. O avaliador foi integrado como
checkpoint explicitamente incompleto; C5 permanece parcial. C2/C3 da missão
de negatividade já estão concluídas; este trabalho segue na certificação
finita C5. Não há PR aberta para este checkpoint.

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

O avaliador genérico, a auditoria local e a publicação pela PR #207 (commit de
prova `fb8bb31ed1fcbb4d1d9c88aceea1dd83539935df`, merge
`27a61e6bebcce178b81b961f507400ed77b96d3b`) estão documentados em
`evidence/rational-boxes/c5-rational-node-evaluator-validation.md`; ainda não
há nenhum nó instanciado nem inclusão de coeficientes provada.

Continuam adiados a lei quantitativa distância × profundidade e os novos
cadernos. Não é necessário calcular a primeira profundidade de falha para a
negatividade eventual já concluída em C2.
