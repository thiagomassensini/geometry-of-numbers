# Retomar primeiro — C5

**MISSÃO:** C5 — certificação finita da primeira janela negativa C2 original
**CURRENT PHASE:** O3 integrada; iniciar O4 (inclusão da fonte original nas caixas)
**CURRENT SUBTASK:** Provar as hipóteses `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes` preservando a cabeça C2, a cauda exponencial exata e a completação original
**LAST VERIFIED THEOREMS:** `sigmaPadeD_signs_at_99_2000_of_source_boxes` e `sigmaPadeD_signs_at_1_10_of_source_boxes`
**LAST COMPILED FILE:** `research/native-moving-schur-sigma/SigmaFiniteRationalIntervalAudit.lean` (Lean 4.32; seis módulos em build limpo; 13 raízes auditadas)
**LAST SUCCESSFUL MERGE:** PR #167, prova racional condicional O3, merge `fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`
**LAST REMOTE SHA:** `origin/main=fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`; Momentos `origin/research/sigma-pade-dimension-depth-20261104=68c9b5f0a196289e28a8e5586146707d27df6b75`
**CURRENT BRANCH:** `codex/c5-finite-c2-certification-20261106`
**MAIN SHA:** `fc17d3b16fd0ed5643cb12ef48c80bb81c81cbd9`
**C5 PRs:** #165 e #166 estão integradas; a PR #2 de Momentos permanece aberta e não foi integrada
**WHAT IS PROVED:** Recorrência polinomial sem divisão, identidade exata com `sigmaPadeD` original, transporte racional por caixas e sinais dos menores estão compilados em Lean. O3 prova os dois padrões de sinais condicionalmente à inclusão dos coeficientes nas caixas.
**WHAT IS CONDITIONAL:** `sigmaPadeD_signs_at_99_2000_of_source_boxes` e `sigmaPadeD_signs_at_1_10_of_source_boxes` exigem hipóteses explícitas de inclusão. A prova de que a fonte satisfaz essas hipóteses segue aberta.
**WHAT IS BLOCKED:** O4: o gerador usa `mpmath.iv`/funções elementares cuja inclusão rigorosa ainda não foi provada em Lean. Isso impede os dois resultados incondicionais de C5.
**NEXT ACTION:** Identificar e provar o menor caminho rigoroso para as inclusões O4.
**EXACT NEXT MATHEMATICAL OBLIGATION:** Provar `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes` para a fonte C2 original, preservando cabeça C2, cauda exata e completação original.
**DO NOT REPEAT:**
- Não refazer C2 eventual, C3, nem a recorrência analítica C4.
- Não redefinir `completedSigmaLogJet`, `sigmaPadeD` ou `completedSigmaDisplacedSourceCoefficient`.
- Não tratar caixas JSON nem saída de `mpmath.iv` como prova de inclusão.
- Não repetir as três gerações intervalares já reproduzidas salvo mudança no código, backend ou limites; os logs estão em `evidence/interval-certificate/`.
- Não usar aproximações de dois/três polos como substituto da fonte C2 completa.
- Não mesclar a PR #2 inteira sem auditar seu escopo.
- Não tocar nos logs/caches não rastreados das demais worktrees.

Detalhes de retomada, pins e estado atual: `SESSION_STATE.md`, `THEOREM_MAP.md`, `OPEN_OBLIGATIONS.md`, `CHECKPOINTS.md` e `evidence/rational-boxes/VALIDATION.md` neste diretório.
