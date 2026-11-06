# Retomar primeiro — C5

**MISSÃO:** C5 — certificação finita da primeira janela negativa C2 original  
**CURRENT PHASE:** Fase 0 concluída; auditoria dos certificados e transporte polinomial Lean a iniciar  
**CURRENT SUBTASK:** Validar o verificador racional publicado e formalizar a recorrência C4 em Lean 4.32  
**LAST VERIFIED THEOREM:** C4: `completedSigmaDisplacedSourceSeries_mul_moments_eq_neg_derivative`  
**LAST COMPILED FILE:** `research/native-moving-schur-sigma/SigmaSourceBezout.lean` (Lean 4.32, pin em `mission-sigma-sign-20261105/evidence/c4-source-bezout/pins-and-sha256.txt`)  
**LAST SUCCESSFUL COMMIT:** `91a1af2f9663d6761a3320e2f06504fe8aaa6776` (base `origin/main`, PR #164)  
**LAST REMOTE SHA:** geometry `origin/main=91a1af2f9663d6761a3320e2f06504fe8aaa6776`; momentos `origin/research/sigma-pade-dimension-depth-20261104=68c9b5f` (SHA completo em `SESSION_STATE.md`)  
**CURRENT BRANCH:** `codex/c5-finite-c2-certification-20261106`  
**MAIN SHA:** `91a1af2f9663d6761a3320e2f06504fe8aaa6776`  
**OPEN PR:** Momentos PR #2 permanece aberta e não auditada para merge; ainda não há PR C5  
**WHAT IS PROVED:** C2 eventual, C3 par/ímpar e C4 fonte deslocada/recorrência/Bézout estão integrados. A recorrência polinomial finita e o transporte de sinal existem no relatório/scripts Python, não como módulo Lean.  
**WHAT IS CONDITIONAL:** Sinais racionais calculados a partir das caixas dos coeficientes, assumindo que a fonte C2 original pertença a essas caixas.  
**WHAT IS BLOCKED:** Inclusão dos coeficientes verdadeiros da fonte original nos intervalos ainda não foi provada por um avaliador intervalar formalmente certificado.  
**EXACT NEXT COMMAND:** `python verify_signs_exact.py coeff_box_d00495_25digits.json && python verify_signs_exact.py coeff_box_d01_25digits.json` a partir do diretório `investigations/c2_first_negative_interval_certificate_20261106/` da worktree de pesquisa Momentos.  
**EXACT NEXT MATHEMATICAL OBLIGATION:** Formalizar `pₙ=c₀^(n+1)·(2hₙ)`, sua recorrência sem divisão e `pₛpₛ₊₂−pₛ₊₁²=4c₀^(2s+4)·sigmaPadeD d s`; então transportar as caixas racionais para os sinais originais.  
**DO NOT REPEAT:**
- Não refazer C2 eventual, C3, nem a recorrência analítica C4.
- Não redefinir `completedSigmaLogJet`, `sigmaPadeD` ou `completedSigmaDisplacedSourceCoefficient`.
- Não tratar caixas JSON nem saída de `mpmath.iv` como prova de inclusão.
- Não usar aproximações de dois/três polos como substituto da fonte C2 completa.
- Não mesclar a PR #2 inteira sem auditar seu escopo.
- Não tocar nos logs/caches não rastreados das demais worktrees.

Detalhes de retomada, pins e estado atual: `SESSION_STATE.md`, `THEOREM_MAP.md`, `OPEN_OBLIGATIONS.md` e `CHECKPOINTS.md` neste diretório.
