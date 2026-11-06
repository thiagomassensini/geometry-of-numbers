# Retomar primeiro — C5

**MISSÃO:** C5 — certificação finita da primeira janela negativa C2 original
**CURRENT PHASE:** Fase 1 (transporte algébrico) integrada; iniciar O3 (verificação racional Lean)
**CURRENT SUBTASK:** Formalizar o propagador intervalar racional e provar os sinais condicionais das duas listas de coeficientes
**LAST VERIFIED THEOREM:** `sigmaPadeD_neg_of_completedSigmaFiniteScaledMoment_minor_neg`
**LAST COMPILED FILE:** `research/native-moving-schur-sigma/SigmaFiniteCoefficientSignTransport.lean` (Lean 4.32; build limpo e auditoria em `evidence/`)
**LAST SUCCESSFUL MERGE:** PR #165; commit de prova `1250a9989e596fa250304d8ec8fd3ae45897e589`; merge `75691edf0e74cc643f098213f60b684476132175`
**LAST REMOTE SHA:** `origin/main=75691edf0e74cc643f098213f60b684476132175`; Momentos `origin/research/sigma-pade-dimension-depth-20261104=68c9b5f0a196289e28a8e5586146707d27df6b75`
**CURRENT BRANCH:** `codex/c5-finite-c2-certification-20261106`
**MAIN SHA:** `75691edf0e74cc643f098213f60b684476132175`
**C5 PR:** #165 está integrada; Momentos PR #2 permanece aberta e não foi integrada
**WHAT IS PROVED:** Recorrência polinomial sem divisão, identidade exata com `sigmaPadeD` original e transportes de sinal estão compilados em Lean para a fonte C4. As três gerações intervalares e os dois verificadores racionais foram reproduzidos.
**WHAT IS CONDITIONAL:** Os sinais finitos seguem das caixas racionais sob a hipótese de que os coeficientes verdadeiros da fonte estejam dentro delas; a inclusão ainda não foi provada.
**WHAT IS BLOCKED:** O transporte algébrico não tem bloqueio. A inclusão da fonte segue aberta porque o gerador usa funções elementares `mpmath.iv` ainda não certificadas em Lean.
**NEXT ACTION:** Implementar O3: intervalos com centro e raio racionais, propagação por multiplicação e recorrência dos menores; manter os sinais como condicionais às caixas até O4.
**EXACT NEXT MATHEMATICAL OBLIGATION:** Formalizar intervalos racionais, propagar as caixas pela recorrência `pₙ` e provar em Lean os padrões `+++++++++++-` e `+++++++++-` sob as hipóteses de caixa; em seguida provar a inclusão dos coeficientes da fonte C2 original.
**DO NOT REPEAT:**
- Não refazer C2 eventual, C3, nem a recorrência analítica C4.
- Não redefinir `completedSigmaLogJet`, `sigmaPadeD` ou `completedSigmaDisplacedSourceCoefficient`.
- Não tratar caixas JSON nem saída de `mpmath.iv` como prova de inclusão.
- Não repetir as três gerações intervalares já reproduzidas salvo mudança no código, backend ou limites; os logs estão em `evidence/interval-certificate/`.
- Não usar aproximações de dois/três polos como substituto da fonte C2 completa.
- Não mesclar a PR #2 inteira sem auditar seu escopo.
- Não tocar nos logs/caches não rastreados das demais worktrees.

Detalhes de retomada, pins e estado atual: `SESSION_STATE.md`, `THEOREM_MAP.md`, `OPEN_OBLIGATIONS.md` e `CHECKPOINTS.md` neste diretório.
