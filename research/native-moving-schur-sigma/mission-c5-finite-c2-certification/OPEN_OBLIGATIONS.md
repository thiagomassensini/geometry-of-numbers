# C5 — obrigações abertas

## O1 — validar o cálculo racional publicado — REPRODUZIDO

Os dois verificadores exatos passaram sobre as caixas JSON rastreadas, com resultados `+++++++++++-` e `+++++++++-`. As três configurações de geração intervalar também foram reproduzidas após conversão local de `gmpy2.mpz` para inteiro Python nativo. Logs e patch estão em `evidence/interval-certificate/`.

Isso confirma a implicação racional condicional às caixas; não confirma que os coeficientes verdadeiros estejam nelas.

## O2 — transporte C4 em Lean — PROVADO E AUDITADO

`SigmaFiniteCoefficientSignTransport.lean` prova a recorrência polinomial sem divisão para `pₙ=c₀^(n+1)Hₙ`, com `Hₙ=2*completedSigmaLogJet d n`, a identidade do determinante original e os dois transportes de sinal. Compila em Lean 4.32; `#print axioms` lista somente `propext`, `Classical.choice`, `Quot.sound`.

## O3 — aritmética intervalar racional formal — PROVADO CONDICIONALMENTE E AUDITADO

Os módulos `SigmaFiniteRationalIntervals`, `SigmaFiniteRationalIntervalBoxes`,
`SigmaFiniteRationalIntervalTransport`, `SigmaFiniteRationalIntervalSigns` e
`SigmaFiniteRationalIntervalCertificates` portam as caixas JSON a bolas racionais
exatas, propagam a recorrência original escalada e certificam cada menor no Lean.
Em `d=99/2000`, provam `0 < D_s` para todo `s<11` e `D_11<0`; em `d=1/10`,
provam `0 < D_s` para todo `s<9` e `D_9<0`, sob as hipóteses explícitas de que
os coeficientes verdadeiros pertencem às respectivas caixas (`sigmaC00495SourceBoxes`
e `sigmaC01SourceBoxes`). A composição termina no `sigmaPadeD` original.

Build Lean 4.32 limpo, com warnings como erros, e auditoria transitiva de 13
raízes passaram. Os únicos axiomas são `propext`, `Classical.choice` e
`Quot.sound`. Comandos, logs, hashes de fontes/oleans e verificador fail-closed
estão em `evidence/rational-boxes/`. A integração por PR ainda está pendente.

## O4 — origem das caixas — ABERTO

Provar inclusões rigorosas dos coeficientes `c₀..c₁₄` em `d=99/2000` e `c₀..c₁₂` em `d=1/10`, preservando cabeça C2 + cauda geométrica exata + completação original. Certificar restos de Hurwitz/Euler–Maclaurin, Stirling, operações elementares, contorno Cauchy/Fourier e todos os domínios usados. A saída Python atual não fecha essa obrigação.

O avaliador foi conferido estruturalmente e as três reproduções passaram, mas
`mpmath.iv`/seu backend e as operações complexas elementares ainda não têm prova
Lean de arredondamento externo. Esse é o primeiro bloqueio concreto à
certificação incondicional: sem provar a inclusão da fonte nas caixas, as
conclusões O3 permanecem condicionais.

## O5 — composição, build, axiomas e publicação — PARCIAL

A Fase 1 foi integrada pela PR #165, merge `75691edf0e74cc643f098213f60b684476132175`.
O3 passou build e auditoria local; sua publicação está pendente. O4 e os teoremas
finais incondicionais seguem abertos.

## Classificação honesta se O4 continuar em aberto

Manter os resultados que dependem das caixas explicitamente condicionais e relatar precisamente qual coeficiente ou camada de funções elementares bloqueia a inclusão. Não declarar `PROVADO — CERTIFICAÇÃO COMPLETA`.
