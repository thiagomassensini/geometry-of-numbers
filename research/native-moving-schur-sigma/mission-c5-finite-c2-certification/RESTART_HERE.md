# Retomar primeiro — C5

**MISSÃO:** C5 — certificação finita da primeira janela negativa C2 original
**CURRENT PHASE:** O3 integrada; O4 em investigação (inclusão da fonte original nas caixas)
**CURRENT SUBTASK:** Obter uma caixa racional quantitativa de `Complex.Gamma` na região Cauchy, comparando Stirling com a identidade de Weierstrass já provada; em seguida compor Hurwitz, o limite Cauchy e a ponte C2 original
**LAST VERIFIED THEOREMS:** `sigmaPadeD_signs_at_99_2000_of_source_boxes` e `sigmaPadeD_signs_at_1_10_of_source_boxes`
**LAST COMPILED FILE:** `research/native-moving-schur-sigma/SigmaFiniteRationalIntervalAudit.lean` (Lean 4.32; seis módulos em build limpo; 13 raízes auditadas)
**LAST SUCCESSFUL MERGE:** PR #168, estado O3 registrado, merge `1bc7318915c3e625ad228c89ff8c300cb07e52c5`
**LAST REMOTE SHA:** `origin/main=1bc7318915c3e625ad228c89ff8c300cb07e52c5`; Momentos `origin/research/sigma-pade-dimension-depth-20261104=68c9b5f0a196289e28a8e5586146707d27df6b75`
**CURRENT BRANCH:** `codex/c5-finite-c2-certification-20261106`
**MAIN SHA:** `1bc7318915c3e625ad228c89ff8c300cb07e52c5`
**C5 PRs:** #165 e #166 estão integradas; a PR #2 de Momentos permanece aberta e não foi integrada
**WHAT IS PROVED:** Recorrência polinomial sem divisão, identidade exata com `sigmaPadeD` original, transporte racional por caixas e sinais dos menores estão compilados em Lean. O3 prova os dois padrões de sinais condicionalmente à inclusão dos coeficientes nas caixas. O motor intervalar formal existente para `log`/`exp` também compila e foi auditado.
**WHAT IS CONDITIONAL:** `sigmaPadeD_signs_at_99_2000_of_source_boxes` e `sigmaPadeD_signs_at_1_10_of_source_boxes` exigem hipóteses explícitas de inclusão. A prova de que a fonte satisfaz essas hipóteses segue aberta.
**WHAT IS OPEN:** O4 ainda não tem inclusão analítica da fonte. A infraestrutura existente cobre bolas racionais, `log` real e `exp` real/complexo, mas ainda não produz uma caixa racional para `Complex.Gamma`.
**NEXT ACTION:** Avaliar a rota de `Zeta23.DigammaSeries.inv_gamma_eq_prod`, que já prova o produto de Weierstrass para `1/Γ`; derive uma caixa de cauda e compare seu custo com formalizar o resto complexo de Stirling.
**EXACT NEXT MATHEMATICAL OBLIGATION:** Incluir `Complex.Gamma (w/2)` numa caixa racional para `0.1495 ≤ Re(w) ≤ 0.9495`, `|Im(w)| ≤ 0.4`. A rota numérica Stirling usa Q=80, p=75; a rota alternativa usa `inv_gamma_eq_prod` e requer limites computáveis para o produto e seu fator exponencial.
**EXACT NEXT COMMAND:** Ler `research/native-moving-schur-sigma/height50-certified/lean/vendor/zeta23/Zeta23/GammaFacts/Series.lean` em torno de `inv_gamma_eq_prod`; comparar os limites da série `wTerm` com a precisão das caixas em `evidence/rational-boxes/`.
**DO NOT REPEAT:**
- Não refazer C2 eventual, C3, nem a recorrência analítica C4.
- Não redefinir `completedSigmaLogJet`, `sigmaPadeD` ou `completedSigmaDisplacedSourceCoefficient`.
- Não tratar caixas JSON nem saída de `mpmath.iv` como prova de inclusão.
- Não repetir as três gerações intervalares já reproduzidas salvo mudança no código, backend ou limites; os logs estão em `evidence/interval-certificate/`.
- Não usar aproximações de dois/três polos como substituto da fonte C2 completa.
- Não mesclar a PR #2 inteira sem auditar seu escopo.
- Não tocar nos logs/caches não rastreados das demais worktrees.

Detalhes de retomada, pins e estado atual: `SESSION_STATE.md`, `THEOREM_MAP.md`, `OPEN_OBLIGATIONS.md`, `CHECKPOINTS.md` e `evidence/rational-boxes/VALIDATION.md` neste diretório.
