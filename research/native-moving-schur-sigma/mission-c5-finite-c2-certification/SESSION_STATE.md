# C5 — estado da sessão

**Atualizado:** 2026-11-06
**Status atual:** C1–C4 e O3 estão integradas. Também estão provados em Lean 4.32 os limites dos pesos escalados de graus `0..14`: grau zero `=1`, grau um `<10^11` e graus `2..14` `<10^145`. A PR #187 integrou a etapa de graus 2–14; commit de prova `6424f4334edd5c776997116403043635fa0c8f83`, merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`. A PR #191 integrou o majorante da fonte `10^100`, merge `88a52ba3a6bda7a78b8317d892b6f7bc640c863f`; nesta continuação, uma cota mais forte `10^13` compilou e passou auditoria local. O4 permanece aberta porque faltam as avaliações certificadas nos 129 nós e a inclusão dos coeficientes C2 nas caixas.

**Checkpoint atual — cota analítica explícita (2026-11-06):** `CarrySigmaObstruction.displacedProductC_norm_le_10pow13_on_ball_39` prova `‖displacedProductC d z‖ ≤ 10^13` para `|d|≤1/10` e `z∈ball(0,39/100)`. O wrapper `10^100` da PR #191 continua disponível. O build limpo Lean 4.32 e a auditoria fail-closed de quatro raízes passaram; somente `propext`, `Classical.choice` e `Quot.sound` aparecem. Detalhes, hashes e logs estão em `evidence/rational-boxes/analytic-bounds-10pow13-validation.md`. Com o contorno `38/100`, a análise exata dá erro de interpolação `<10^-501` e amplificação do erro Gamma `<10^-135`. Este checkpoint é parcial: nenhuma avaliação dos 129 nós nem inclusão nas caixas foi concluída.
**Checkpoint de graus 2–14 (2026-11-06):** `c5LagrangeBasis_zeroIndex_coeff_abs_le_two_pow`, `c5LagrangeBasis_nonzeroIndex_coeff_abs_le_weight`, `c5InterpolationCoeffAbsSum_le_four_mul_two_pow` e `c5InterpolationWeightSum_lt_ten_145` formalizam a cota uniforme simbólica. Build limpo: `c5-interpolation-degree2-14-final-clean-build.log`, `BUILD_EXIT=0`. A auditoria das 23 raízes aceita apenas `propext`, `Classical.choice` e `Quot.sound`; logs e hashes estão preservados. O checkpoint permanece explicitamente incompleto e não prova inclusão de caixas.
**Checkpoint de grau um (2026-11-06):** a alteração simbólica de `SigmaRationalInterpolation.lean` passou build Lean 4.32 limpo e auditoria fail-closed de 21 raízes. Logs e hashes estão em `evidence/rational-boxes/degree1-weight-bound-validation.md`; tentativas anteriores incompletas e a prova rejeitada com `native_decide` foram mantidas como histórico.
**Publicação do limite de grau um:** PR #185, commit de prova `90a208df98e74a7c5ab1fe83a9ef0fc90c3d3cb6`, merge `c840ba35711ac8f938fa24c191f2af60f505480d`. O checkpoint explicitamente incompleto foi publicado separadamente pela PR #184, merge `5528ddc8093a22682c87f3f9c6575e30e90a7011`.
**Branch C5 de trabalho:** o passo estrutural de grau um foi publicado no commit `0a188c9d71a1a54bdf446ec753609fdde8326bc8`, integrado pela PR #181. A branch remota de prova foi removida após o merge; retomar a partir da `main` atual e abrir uma branch nova.
**Main geometry no início da auditoria O4:** `1bc7318915c3e625ad228c89ff8c300cb07e52c5` (merge da PR #168).
**Última prova geometry integrada:** PR #187, limite dos pesos escalados de graus 2–14, merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
**Registro de estado anterior à PR #177:** PR #176, merge `ac84c9302ae608e39c742f856ad361921653f268`.
**Última prova integrada:** PR #187, limites dos pesos escalados de graus 2–14, merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
**Main geometry após a PR #187:** `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
**Checkpoint de estado pós-PR #181:** PR #182, merge `8f8b9da2b8c1e8f3b8d1290608c8b2abffe9c285`.
**Main geometry no checkpoint de estado:** `8f8b9da2b8c1e8f3b8d1290608c8b2abffe9c285`.
**Repositório geometry no checkout de pesquisa original:** branch `agent/native-moving-schur-sigma`, HEAD `9392ebac9930f5d11c56f595556080e8ab1de809`, com logs/caches não rastreados preservados. A `main` remota consultada após a PR #187 está em `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
**Repositório Momentos:** checkout local `main` em `05c9314d59306383baa55ed3be80ab950e799e97`; branch remota de pesquisa `origin/research/sigma-pade-dimension-depth-20261104` em `68c9b5f0a196289e28a8e5586146707d27df6b75`. PR #2 está OPEN e não foi integrada.

## Inventário de trabalho anterior

- C2, C3 e C4 constam integradas à main geometry. C4 está documentada em `mission-sigma-sign-20261105/evidence/c4-source-bezout/VALIDATION.md`.
- `SigmaSourceBezout.lean` já define `completedSigmaDisplacedSourceCoefficient` e `completedSigmaDisplacedMoment`; prova `C_d·H_d=-C_d′`, `H_d(n)=2*completedSigmaLogJet d n`, e `c₀>0` para os deslocamentos no domínio. O fator 2 deve permanecer explícito.
- Foi criado `SigmaFiniteCoefficientSignTransport.lean`. Em Lean 4.32 prova a recorrência polinomial sem divisão, a identidade exata com `CarrySigmaPade.sigmaPadeD` original e os transportes de sinais positivo/negativo. `SigmaFiniteCoefficientSignTransportAudit.lean` registra os quatro `#print axioms`; footprint: `propext`, `Classical.choice`, `Quot.sound`.
- A Fase 1 foi integrada pela PR #165, com commit de prova `1250a9989e596fa250304d8ec8fd3ae45897e589` e merge `75691edf0e74cc643f098213f60b684476132175`. Não houve status checks hospedados; build Lean 4.32 e auditoria local estão preservados em `evidence/`.
- Os dois JSONs racionais passaram no verificador exato, produzindo `+++++++++++-` e `+++++++++-` condicionais às caixas. As três gerações prescritas foram reproduzidas após ajuste local de compatibilidade (`gmpy2.mpz`→`int`) no checkout Momentos isolado. Patch e falha original estão preservados em `evidence/interval-certificate/`; a branch remota Momentos não foi alterada.
- A ponte geométrica `canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar` foi consultada na revisão carry pinada `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O avaliador usa Hurwitz somente para avaliar a cauda exata e mantém a cabeça C2 e a completação original.
- O diretório `research/c3-fourteenth-tail/` e seus módulos dizem respeito a outro certificado finito; foram observados durante a busca e não são reutilizados sem prova de correspondência à fonte C2 desta missão.
- Há várias worktrees com alterações/logs paralelos. A branch de pesquisa original e caches/logs não rastreados foram mantidos intactos; C5 usa worktree nova.

## O que está provado / condicional / pendente

**PROVADO e integrado (contexto):** C2 eventual em `d=1/5`; C3 setores par e ímpar; C4 recorrência original e equivalência Bézout. Isso não prova os sinais finitos desta missão em `d=99/2000` ou `d=1/10`.

**PROVADO em Lean nesta branch:** a recorrência `p_n` sem divisão, a identidade `p_s p_(s+2)-p_(s+1)^2 = 4*c_0^(2*s+4)*sigmaPadeD d s` e os dois lemas genéricos de transporte de sinal. Lean 4.32 e auditoria de axiomas passaram.

**PROVADO CONDICIONALMENTE e integrado pela PR #167:** as caixas exatas são propagadas pela recorrência polinomial da Fase 1; os limites inferiores dos menores são positivos para `s<11` em `99/2000` e para `s<9` em `1/10`, e os limites superiores finais são negativos em `s=11` e `s=9`. Sob hipóteses explícitas de inclusão (`sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`), isso prova os sinais de `sigmaPadeD` original. Merge: `fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`. Build limpo e auditoria de 13 raízes passaram; só aparecem `propext`, `Classical.choice`, `Quot.sound`. Ver `evidence/rational-boxes/VALIDATION.md`.

**PENDENTE:** provar que os coeficientes verdadeiros da fonte C2 original pertencem às caixas; depois compor os dois teoremas finais incondicionais. A primeira obrigação aberta agora é O4, não O3.

**O4 — avanço de infraestrutura:** os módulos existentes `ZetaLean.Rigor`, `ZetaLean.IntervalExp` e `ZetaLean.IntervalCExp` foram recompilados em Lean 4.32 com warnings como erros. Aritmética retangular racional, `log` real, `exp` real/complexo e `m^{-s}` têm inclusões kernel-checked. Quatro raízes foram auditadas e dependem apenas de `propext`, `Classical.choice`, `Quot.sound`.

O checkpoint reprodutível dessa auditoria foi integrado pela PR #169; merge na main `75782fb8b7fb00bd273bd99f78c337f98439e934`. Os logs, comandos, hashes de fontes e `.olean` agora estão rastreados em `evidence/rational-boxes/`.

**Subpasso Gamma integrado pela PR #171:** `SigmaC5Gamma.gamma_finite_512_error` demonstra erro `≤10⁻³²` para `gammaFinite 512 81` no domínio `1495/20000 ≤ Re(z) ≤ 1`; build e auditoria de oito raízes passaram.

**Subpasso Gamma de precisão alta integrado pela PR #173:** `gamma_finite_1024_240_error` demonstra erro `≤10⁻⁹⁹` para `gammaFinite 1024 240` no mesmo domínio. Build Lean 4.32 com warnings como erros e auditoria de dez raízes passaram. Merge: `72586b6223579ee1b37a6077ad6f2a0eceaf919c`. Logs e hashes estão em `evidence/rational-boxes/`.

**Subpasso Gamma para interpolação racional integrado pela PR #175:** `gamma_finite_3072_620_error` demonstra erro `≤10⁻²⁵⁹` para `gammaFinite 3072 620`, no domínio `1495/20000 ≤ Re(z) ≤ 1`. Build Lean 4.32 e auditoria de doze raízes passaram. Merge: `992ab31c3aacdf3b95b3c02fe58f5f3d529c0cec`. Logs e hashes estão em `evidence/rational-boxes/`.

**Primeiro lema O4 ainda ausente:** inclusão em caixas racionais estreitas da expressão finita `gammaFinite 3072 620 z` nos valores usados para os coeficientes. A ponte Euler já fica abaixo da precisão necessária; permanece a avaliação com cancelamento da soma finita, a avaliação Hurwitz e a composição com a fonte C2.

**Identidade algébrica de interpolação:** `SigmaRationalInterpolation.lean` define os 129 nós `j²`, prova que são distintos e formaliza a reconstrução exata de polinômios racionais de grau menor que 129 e a fórmula dos coeficientes pela interpolação de Lagrange. Build Lean 4.32 limpo e auditoria atualizada de 21 raízes passaram; apenas `propext`, `Classical.choice` e `Quot.sound` aparecem.

**Grau zero dos pesos provado:** o coeficiente constante da base de Lagrange em `j=0` é `1`, as demais bases têm coeficiente constante `0`, e `c5InterpolationWeightSum_zero_eq_one` conclui que a soma absoluta do peso escalado de grau zero é exatamente `1`.

**Pesos de graus 0–14 provados:** grau zero tem soma absoluta exatamente `1`; grau um satisfaz `<10^11`; para cada `2≤n≤14`, `c5InterpolationWeightSum_lt_ten_145` prova `<10^145`. A prova de grau um integrada pela PR #185 está descrita em `degree1-weight-bound-validation.md`; a prova local mais recente está em `degree2-14-weight-bound-validation.md`. A cota analítica da fonte e a inclusão C2 nas caixas continuam abertas.

**Publicação do grau um:** PR #185, merge `c840ba35711ac8f938fa24c191f2af60f505480d`; validação limpa e auditoria de 21 raízes em `evidence/rational-boxes/degree1-weight-bound-validation.md`. O4 continua aberta.

## Checkpoint O4 — domínio analítico da fonte deslocada (2026-11-06)

**PROVADO localmente em Lean 4.32:** `SigmaC5SourceAnalytic.lean` estabelece
`displacedProductC_analyticOnNhd_ball` para `|d|≤1/10` e disco aberto de raio
`2/5`, com especializações em `99/2000` e `1/10`. A prova transporta os dois
argumentos da característica completada original ao domínio de altura do
Carry; não muda a fonte C2.

Build limpo com `warningAsError=true` passou. O checker fail-closed auditou as
quatro declarações públicas e aceitou somente `propext`, `Classical.choice` e
`Quot.sound`. Fonte, log da tentativa inicial com cache errado, log da execução
que passou, saída do checker e hashes estão em
`evidence/rational-boxes/source-analytic-domain-validation.md`.

Este resultado prova apenas analiticidade no domínio. **Não** estabelece a
cota de módulo necessária à interpolação, não certifica os valores nos 129 nós
e não prova as inclusões dos coeficientes nas caixas. A obrigação O4 continua
aberta. Próxima obrigação: provar uma cota numérica explícita a partir da
completação C2 original, tratando os cancelamentos nos pontos `s=0` e `s=1`.

**Git publicado:** PR #189, commit de prova
`e0272bfc9099031cb127ea0db8874900d9e8eca1`, merge na `main`
`3513a3b3854b105419d4f2cef245efac7ce88ba0`. A branch pós-merge de estado é
`codex/c5-state-after-pr189-20261106`. Não há PR aberta.

## Validação reproduzida

- A: `d=.0495`, `L=0`, `N=1024`, `r/R=.30/.40`: `+++++++++++-`.
- A independente: `d=.0495`, `L=12`, `N=512`, `r/R=.20/.40`: `+++++++++++-`.
- B: `d=.1`, `L=12`, `N=512`, `r/R=.15/.30`: `+++++++++-`.
- Os logs, JSONs, hashes e patch de compatibilidade estão em `evidence/interval-certificate/`.
- Build limpo e auditoria dos módulos de transporte algébrico estão em `evidence/build-transport-clean.log` e `evidence/axiom-audit-transport-clean.log`; build e auditoria de O3 estão em `evidence/rational-boxes/`.

## Regras de estado

Nenhuma caixa JSON será elevada a fato sobre os coeficientes sem uma prova de inclusão. O3 conclui os sinais apenas sob as hipóteses explícitas de caixa; O4 ainda bloqueia os teoremas incondicionais dos dois deslocamentos.
