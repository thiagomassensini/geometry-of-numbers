# Retomar primeiro — C5

**MISSÃO:** C5 — certificação finita da primeira janela negativa C2 original
**CURRENT PHASE:** O3 integrada; O4 em investigação (inclusão da fonte original nas caixas)
**CURRENT SUBTASK:** Enquadrar racionalmente `gammaFinite 1024 240 z` nos discos Cauchy; depois compor Hurwitz, Cauchy/Fourier e a ponte C2 original
**LAST VERIFIED THEOREMS:** `sigmaPadeD_signs_at_99_2000_of_source_boxes` e `sigmaPadeD_signs_at_1_10_of_source_boxes`
**LAST COMPILED FILE:** `SigmaGammaEulerIntegral.lean` e `gamma-euler-audit.lean` (Lean 4.32; novo erro uniforme `10⁻⁹⁹`; dez raízes auditadas)
**LAST SUCCESSFUL MERGE:** PR #173, ponte Euler-Gamma a `10⁻⁹⁹`, merge `72586b6223579ee1b37a6077ad6f2a0eceaf919c`
**LAST REMOTE SHA:** `origin/main=72586b6223579ee1b37a6077ad6f2a0eceaf919c`; Momentos `origin/research/sigma-pade-dimension-depth-20261104=68c9b5f0a196289e28a8e5586146707d27df6b75`
**CURRENT BRANCH:** `codex/c5-finite-c2-certification-20261106`
**MAIN SHA:** `72586b6223579ee1b37a6077ad6f2a0eceaf919c`
**C5 PRs:** #165–#173 estão integradas; a PR #2 de Momentos permanece aberta e não foi integrada
**WHAT IS PROVED:** Recorrência polinomial sem divisão, identidade exata com `sigmaPadeD` original, transporte racional por caixas e sinais dos menores estão compilados em Lean. O3 prova os dois padrões de sinais condicionalmente à inclusão dos coeficientes nas caixas. PR #171 integrou a ponte Euler-Gamma a erro `10⁻³²`; PR #173 melhora o erro para `10⁻⁹⁹`.
**WHAT IS CONDITIONAL:** `sigmaPadeD_signs_at_99_2000_of_source_boxes` e `sigmaPadeD_signs_at_1_10_of_source_boxes` exigem hipóteses explícitas de inclusão. A prova de que a fonte satisfaz essas hipóteses segue aberta.
**WHAT IS OPEN:** O4 ainda não prova as inclusões das caixas da fonte. A ponte Euler está a erro `10⁻⁹⁹`, mas `gammaFinite 1024 240` ainda não tem caixas racionais estreitas.
**NEXT ACTION:** Derivar os coeficientes Taylor racionais de `gammaFinite 1024 240 z` em torno do centro Cauchy e provar uma caixa racional uniforme nos discos exigidos.
**EXACT NEXT MATHEMATICAL OBLIGATION:** Provar caixas racionais para `Complex.Gamma z` nos discos Cauchy usando `gamma_finite_1024_240_error`; depois compor Hurwitz e a extração Cauchy/Fourier.
**EXACT NEXT COMMAND:** Ler `SigmaGammaEulerIntegral.lean`, definir a expansão local racional de `gammaFinite 1024 240` e fechar seu resto uniforme antes da avaliação intervalar.
**DO NOT REPEAT:**
- Não refazer C2 eventual, C3, nem a recorrência analítica C4.
- Não redefinir `completedSigmaLogJet`, `sigmaPadeD` ou `completedSigmaDisplacedSourceCoefficient`.
- Não tratar caixas JSON nem saída de `mpmath.iv` como prova de inclusão.
- Não repetir as três gerações intervalares já reproduzidas salvo mudança no código, backend ou limites; os logs estão em `evidence/interval-certificate/`.
- Não usar aproximações de dois/três polos como substituto da fonte C2 completa.
- Não mesclar a PR #2 inteira sem auditar seu escopo.
- Não tocar nos logs/caches não rastreados das demais worktrees.

Detalhes de retomada, pins e estado atual: `SESSION_STATE.md`, `THEOREM_MAP.md`, `OPEN_OBLIGATIONS.md`, `CHECKPOINTS.md` e `evidence/rational-boxes/VALIDATION.md` neste diretório.
