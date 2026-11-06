# C5 — estado da sessão

**Atualizado:** 2026-11-06
**Status:** inventário, reprodução intervalar, transporte algébrico e O3 racional formal concluídos e integrados; as pontes Euler-Gamma de precisão `10⁻³²`, `10⁻⁹⁹` e `10⁻²⁵⁹` estão integradas; as caixas racionais de `gammaFinite` e a inclusão da fonte C2 seguem pendentes.
**Branch C5 de trabalho:** `codex/c5-finite-c2-certification-20261106`; Fase 1 integrada pela PR #165 e O3 pela PR #167.
**Main geometry no início da auditoria O4:** `1bc7318915c3e625ad228c89ff8c300cb07e52c5` (merge da PR #168).
**Último merge geometry:** PR #175, ponte Euler-Gamma para interpolação, `992ab31c3aacdf3b95b3c02fe58f5f3d529c0cec`.
**Main geometry após a prova de precisão para interpolação:** `992ab31c3aacdf3b95b3c02fe58f5f3d529c0cec`.
**Repositório geometry no checkout de pesquisa original:** branch `agent/native-moving-schur-sigma`, HEAD `9392ebac9930f5d11c56f595556080e8ab1de809`, com logs/caches não rastreados preservados.
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

## Validação reproduzida

- A: `d=.0495`, `L=0`, `N=1024`, `r/R=.30/.40`: `+++++++++++-`.
- A independente: `d=.0495`, `L=12`, `N=512`, `r/R=.20/.40`: `+++++++++++-`.
- B: `d=.1`, `L=12`, `N=512`, `r/R=.15/.30`: `+++++++++-`.
- Os logs, JSONs, hashes e patch de compatibilidade estão em `evidence/interval-certificate/`.
- Build limpo e auditoria dos módulos de transporte algébrico estão em `evidence/build-transport-clean.log` e `evidence/axiom-audit-transport-clean.log`; build e auditoria de O3 estão em `evidence/rational-boxes/`.

## Regras de estado

Nenhuma caixa JSON será elevada a fato sobre os coeficientes sem uma prova de inclusão. O3 conclui os sinais apenas sob as hipóteses explícitas de caixa; O4 ainda bloqueia os teoremas incondicionais dos dois deslocamentos.
