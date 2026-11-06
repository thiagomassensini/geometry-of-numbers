# C5 — estado da sessão

**Atualizado:** 2026-11-06
**Status:** inventário, reprodução intervalar e transporte algébrico C5 concluídos; checker racional Lean e inclusões da fonte pendentes.
**Branch de trabalho:** `codex/c5-finite-c2-certification-20261106`, baseada em `origin/main`; prova algébrica no commit `1250a9989e596fa250304d8ec8fd3ae45897e589`, já enviada ao remoto.
**Main geometry:** `91a1af2f9663d6761a3320e2f06504fe8aaa6776` (PR #164).
**Repositório geometry no checkout de pesquisa original:** branch `agent/native-moving-schur-sigma`, HEAD `9392ebac9930f5d11c56f595556080e8ab1de809`, com logs/caches não rastreados preservados.
**Repositório Momentos:** checkout local `main` em `05c9314d59306383baa55ed3be80ab950e799e97`; branch remota de pesquisa `origin/research/sigma-pade-dimension-depth-20261104` em `68c9b5f0a196289e28a8e5586146707d27df6b75`. PR #2 está OPEN e não foi integrada.

## Inventário de trabalho anterior

- C2, C3 e C4 constam integradas à main geometry. C4 está documentada em `mission-sigma-sign-20261105/evidence/c4-source-bezout/VALIDATION.md`.
- `SigmaSourceBezout.lean` já define `completedSigmaDisplacedSourceCoefficient` e `completedSigmaDisplacedMoment`; prova `C_d·H_d=-C_d′`, `H_d(n)=2*completedSigmaLogJet d n`, e `c₀>0` para os deslocamentos no domínio. O fator 2 deve permanecer explícito.
- Foi criado `SigmaFiniteCoefficientSignTransport.lean`. Em Lean 4.32 prova a recorrência polinomial sem divisão, a identidade exata com `CarrySigmaPade.sigmaPadeD` original e os transportes de sinais positivo/negativo. `SigmaFiniteCoefficientSignTransportAudit.lean` registra os quatro `#print axioms`; footprint: `propext`, `Classical.choice`, `Quot.sound`.
- Os dois JSONs racionais passaram no verificador exato, produzindo `+++++++++++-` e `+++++++++-` condicionais às caixas. As três gerações prescritas foram reproduzidas após ajuste local de compatibilidade (`gmpy2.mpz`→`int`) no checkout Momentos isolado. Patch e falha original estão preservados em `evidence/interval-certificate/`; a branch remota Momentos não foi alterada.
- A ponte geométrica `canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar` foi consultada na revisão carry pinada `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O avaliador usa Hurwitz somente para avaliar a cauda exata e mantém a cabeça C2 e a completação original.
- O diretório `research/c3-fourteenth-tail/` e seus módulos dizem respeito a outro certificado finito; foram observados durante a busca e não são reutilizados sem prova de correspondência à fonte C2 desta missão.
- Há várias worktrees com alterações/logs paralelos. A branch de pesquisa original e caches/logs não rastreados foram mantidos intactos; C5 usa worktree nova.

## O que está provado / condicional / pendente

**PROVADO e integrado (contexto):** C2 eventual em `d=1/5`; C3 setores par e ímpar; C4 recorrência original e equivalência Bézout. Isso não prova os sinais finitos desta missão em `d=99/2000` ou `d=1/10`.

**PROVADO em Lean nesta branch:** a recorrência `p_n` sem divisão, a identidade `p_s p_(s+2)-p_(s+1)^2 = 4*c_0^(2*s+4)*sigmaPadeD d s` e os dois lemas genéricos de transporte de sinal. Lean 4.32 e auditoria de axiomas passaram.

**NUMÉRICO/INTERVALAR condicional:** as rotinas publicadas indicam `+++++++++++-` em `d=0.0495` e `+++++++++-` em `d=0.1`, supondo as caixas dos coeficientes. Os dois verificadores racionais e as três execuções intervalares foram reproduzidos.

**PENDENTE:** formalizar em Lean a propagação racional das caixas e os sinais condicionais; demonstrar que os coeficientes verdadeiros da fonte original pertencem às caixas; compor os dois teoremas finais incondicionais.

## Validação reproduzida

- A: `d=.0495`, `L=0`, `N=1024`, `r/R=.30/.40`: `+++++++++++-`.
- A independente: `d=.0495`, `L=12`, `N=512`, `r/R=.20/.40`: `+++++++++++-`.
- B: `d=.1`, `L=12`, `N=512`, `r/R=.15/.30`: `+++++++++-`.
- Os logs, JSONs, hashes e patch de compatibilidade estão em `evidence/interval-certificate/`.
- Build limpo e auditoria dos módulos de transporte Lean estão em `evidence/build-transport-clean.log` e `evidence/axiom-audit-transport-clean.log`.

## Regras de estado

Nenhuma caixa JSON será elevada a fato sobre os coeficientes sem uma prova de inclusão. O transporte C5 atual usa o `sigmaPadeD` original, mas ainda não conclui os sinais finitos dos dois deslocamentos.
