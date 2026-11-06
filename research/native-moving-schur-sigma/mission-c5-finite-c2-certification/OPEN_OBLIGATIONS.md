# C5 — obrigações abertas

## O1 — validar o cálculo racional publicado — REPRODUZIDO

Os dois verificadores exatos passaram sobre as caixas JSON rastreadas, com resultados `+++++++++++-` e `+++++++++-`. As três configurações de geração intervalar também foram reproduzidas após conversão local de `gmpy2.mpz` para inteiro Python nativo. Logs e patch estão em `evidence/interval-certificate/`.

Isso confirma a implicação racional condicional às caixas; não confirma que os coeficientes verdadeiros estejam nelas.

## O2 — transporte C4 em Lean — PROVADO E AUDITADO

`SigmaFiniteCoefficientSignTransport.lean` prova a recorrência polinomial sem divisão para `pₙ=c₀^(n+1)Hₙ`, com `Hₙ=2*completedSigmaLogJet d n`, a identidade do determinante original e os dois transportes de sinal. Compila em Lean 4.32; `#print axioms` lista somente `propext`, `Classical.choice`, `Quot.sound`.

## O3 — aritmética intervalar racional formal — ABERTO

Portar as duas caixas a intervalos racionais e formalizar a recorrência `p_n`, a inclusão dos menores polinomiais e a exclusão de zero para todos os índices solicitados. Float não pode decidir sinal. Os sinais condicionais Python ainda não estão no kernel Lean.

## O4 — origem das caixas — ABERTO

Provar inclusões rigorosas dos coeficientes `c₀..c₁₄` em `d=99/2000` e `c₀..c₁₂` em `d=1/10`, preservando cabeça C2 + cauda geométrica exata + completação original. Certificar restos de Hurwitz/Euler–Maclaurin, Stirling, operações elementares, contorno Cauchy/Fourier e todos os domínios usados. A saída Python atual não fecha essa obrigação.

O avaliador foi conferido estruturalmente e as três reproduções passaram, mas `mpmath.iv`/seu backend e as operações complexas elementares ainda não têm prova Lean de arredondamento externo. Esse é o primeiro bloqueio concreto à certificação incondicional.

## O5 — composição, build, axiomas e publicação — PARCIAL

A Fase 1 foi compilada/auditada e integrada pela PR #165, merge `75691edf0e74cc643f098213f60b684476132175`. Ainda faltam o build/auditoria das fases O3/O4 e dos teoremas finais.

## Classificação honesta se O4 continuar em aberto

Manter os resultados que dependem das caixas explicitamente condicionais e relatar precisamente qual coeficiente ou camada de funções elementares bloqueia a inclusão. Não declarar `PROVADO — CERTIFICAÇÃO COMPLETA`.
