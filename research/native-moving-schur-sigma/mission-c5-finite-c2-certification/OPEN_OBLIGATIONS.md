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
`Quot.sound`. A etapa foi integrada pela PR #167, merge
`fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`. Comandos, logs, hashes de
fontes/oleans e verificador fail-closed estão em `evidence/rational-boxes/`.

## O4 — origem das caixas — ABERTO

Provar inclusões rigorosas dos coeficientes `c₀..c₁₄` em `d=99/2000` e `c₀..c₁₂` em `d=1/10`, preservando cabeça C2 + cauda geométrica exata + completação original. Certificar a avaliação racional estreita da expressão Gamma finita, a cauda Hurwitz/Euler–Maclaurin e o contorno Cauchy/Fourier, com todos os domínios usados. A saída Python atual não fecha essa obrigação.

O avaliador foi conferido estruturalmente e as três reproduções passaram, mas
`mpmath.iv`/seu backend e as operações complexas elementares ainda não têm prova
Lean de arredondamento externo. Esse é o primeiro bloqueio concreto à
certificação incondicional: sem provar a inclusão da fonte nas caixas, as
conclusões O3 permanecem condicionais.

Uma busca adicional encontrou e recompilou a infraestrutura formal
`ZetaLean.Rigor`, `ZetaLean.IntervalExp` e `ZetaLean.IntervalCExp`, que já
certifica aritmética retangular racional, `log` real, `exp` real/complexo e
`m^{-s}`. A auditoria de quatro raízes retornou somente axiomas padrão; os logs
estão em `evidence/rational-boxes/reused-interval-audit.log`.

**Subpasso de Gamma concluído em Lean:** `SigmaGammaEulerIntegral.lean`
prova que a Gamma original fica a distância no máximo `10⁻³²` da expressão
finita `gammaFinite 512 81 z`, uniformemente para
`1495/20000 ≤ Re(z) ≤ 1`. A prova usa a integral de Euler, limita o erro da
exponencial truncada no trecho compacto e mantém a cauda infinita com limite
`exp(-81)`. As oito raízes auditadas dependem somente de `propext`,
`Classical.choice` e `Quot.sound`.

**Primeiro subproblema analítico ainda em aberto:** produzir caixas racionais
estreitas para `gammaFinite 512 81 z` nas caixas complexas do contorno. A soma
direta tem cancelamento grande; a próxima etapa deve calcular os coeficientes
Taylor racionais da expressão finita antes de aplicar a aritmética intervalar e
certificar o resto da expansão. A identidade formal
`Zeta23.DigammaSeries.inv_gamma_eq_prod` continua sendo uma alternativa. Depois
será preciso compor Hurwitz e Cauchy/Fourier com a ponte C2 exata. Não há prova
de `sigmaC00495SourceBoxes` nem de `sigmaC01SourceBoxes` nesta etapa.

## O5 — composição, build, axiomas e publicação — PARCIAL

A Fase 1 foi integrada pela PR #165, merge `75691edf0e74cc643f098213f60b684476132175`;
O3 foi integrada pela PR #167, merge `fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`.
O4 e os teoremas finais incondicionais seguem abertos.

## Classificação honesta se O4 continuar em aberto

Manter os resultados que dependem das caixas explicitamente condicionais e relatar precisamente qual coeficiente ou camada de funções elementares bloqueia a inclusão. Não declarar `PROVADO — CERTIFICAÇÃO COMPLETA`.
