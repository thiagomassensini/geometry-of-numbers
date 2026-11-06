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

**Ponte Euler-Gamma de alta precisão integrada pela PR #173:** `SigmaGammaEulerIntegral.lean`
prova que, para `1495/20000 ≤ Re(z) ≤ 1`, a Gamma original fica a distância no
máximo `10⁻⁹⁹` da expressão finita `gammaFinite 1024 240 z`. O erro Taylor do
trecho compacto é `≤10⁻¹²⁰` e a cauda é `≤exp(-240)≤10⁻¹⁰⁰`. O build Lean 4.32
e a auditoria de dez raízes passaram, com apenas `propext`, `Classical.choice`
e `Quot.sound`. Merge: `72586b6223579ee1b37a6077ad6f2a0eceaf919c`.

**Primeiro subproblema analítico ainda em aberto:** produzir caixas racionais
estreitas para `gammaFinite 3072 620 z` nos pontos racionais de interpolação. A soma
direta tem cancelamento grande; a próxima etapa deve calcular os coeficientes
Taylor racionais da expressão finita antes de aplicar a aritmética intervalar e
certificar o resto da expansão. A identidade formal
`Zeta23.DigammaSeries.inv_gamma_eq_prod` continua sendo uma alternativa. Depois
será preciso compor Hurwitz e Cauchy/Fourier com a ponte C2 exata. Não há prova
de `sigmaC00495SourceBoxes` nem de `sigmaC01SourceBoxes` nesta etapa.

**Ponte Gamma de interpolação, integrada pela PR #175:**
`gamma_finite_3072_620_error` melhora o erro absoluto para `10⁻²⁵⁹` e tem build
Lean 4.32/auditoria de doze raízes. Merge `992ab31c3aacdf3b95b3c02fe58f5f3d529c0cec`.
Uma exploração exata racional sugere evitar a quadratura trigonométrica:
interpolar a densidade par em 129 pontos racionais `t_j=j/100000`. O novo módulo
`SigmaRationalInterpolation.lean` prova que nós distintos recuperam exatamente
qualquer polinômio racional de grau menor que 129 e formaliza a identidade dos
coeficientes com as somas ponderadas de Lagrange. Isso é somente o passo
algébrico. `c5InterpolationWeightSum_zero_eq_one` prova que o peso escalado de
grau zero soma exatamente `1`; os limites calculados em Python (menores que
`10^124` para graus até 14) ainda não foram provados para os graus `1..14` no
Lean. Para grau um, `c5LagrangeBasis_derivative_eval_zero` expressa os
coeficientes por uma soma de derivadas e produtos finitos; a tentativa de fechar
o limite numérico por expansão direta atingiu o limite de passos de `simp`.
Comando e erro estão em `evidence/rational-boxes/interpolation-weight-degree1-prototype.log`.
Também seguem pendentes a cota analítica
`|completedSigmaDensity d t|≤10^100` no disco de raio `2/5` e a avaliação
rigorosa da fonte nos pontos. A análise exploratória está em
`analyze_rational_interpolation.py` e
`evidence/rational-boxes/rational-interpolation-analysis.log`; build e auditoria
da identidade algébrica estão em `evidence/rational-boxes/VALIDATION.md`.

## O5 — composição, build, axiomas e publicação — PARCIAL

A Fase 1 foi integrada pela PR #165, merge `75691edf0e74cc643f098213f60b684476132175`;
O3 foi integrada pela PR #167, merge `fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`.
O lema algébrico dos 129 nós foi integrado pela PR #177, merge
`0702371cff0c6016eae9eaa0aa9331ae95483456`. O4, a inclusão das caixas e os
teoremas finais incondicionais seguem abertos. O checkpoint de estado pós-PR
#177 foi integrado pela PR #178, merge `7ad7e29195790eedda01645e71e5c52edf1b4e6b`.
A soma exata do peso escalado de grau zero foi integrada pela PR #179, merge
`f6a2298b92cbfddad77abe512d73387efea4e870`; os graus positivos e O4 permanecem
abertos. O estado pós-PR #179 foi registrado pela PR #180, merge
`de95637d38d5e6d5488342cd5141b88233be6eb7`. A estrutura derivativa de grau um
foi integrada pela PR #181, merge
`7460497307e7ed0ffb47ef1ac96b096e9b410472`; a desigualdade numérica dos pesos
continua em aberto e O4 permanece incompleta.
O estado pós-PR #181 foi registrado pela PR #182, merge
`8f8b9da2b8c1e8f3b8d1290608c8b2abffe9c285`.

## Classificação honesta se O4 continuar em aberto

Manter os resultados que dependem das caixas explicitamente condicionais e relatar precisamente qual coeficiente ou camada de funções elementares bloqueia a inclusão. Não declarar `PROVADO — CERTIFICAÇÃO COMPLETA`.
