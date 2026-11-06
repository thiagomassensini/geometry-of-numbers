# Retomar primeiro — C5

**MISSÃO:** C5 — certificação finita da primeira janela negativa C2 original
**CURRENT PHASE:** O3 integrada; O4 em investigação (inclusão da fonte original nas caixas)
**CURRENT SUBTASK:** Enquadrar racionalmente a expressão finita `gammaFinite 512 81 z` nos discos Cauchy, usando a aproximação Euler-Gamma já provada; em seguida compor Hurwitz, Cauchy/Fourier e a ponte C2 original
**LAST VERIFIED THEOREMS:** `sigmaPadeD_signs_at_99_2000_of_source_boxes` e `sigmaPadeD_signs_at_1_10_of_source_boxes`
**LAST COMPILED FILE:** `research/native-moving-schur-sigma/SigmaGammaEulerIntegral.lean` e `gamma-euler-audit.lean` (Lean 4.32; erro uniforme `10⁻³²`; oito raízes auditadas)
**LAST SUCCESSFUL MERGE:** PR #171, ponte Euler-Gamma, merge `a585de1d4df0b093ef4221cf576a9a87a057652a`
**LAST REMOTE SHA:** `origin/main=a585de1d4df0b093ef4221cf576a9a87a057652a`; Momentos `origin/research/sigma-pade-dimension-depth-20261104=68c9b5f0a196289e28a8e5586146707d27df6b75`
**CURRENT BRANCH:** `codex/c5-finite-c2-certification-20261106`
**MAIN SHA:** `a585de1d4df0b093ef4221cf576a9a87a057652a`
**C5 PRs:** #165–#171 estão integradas; a PR #2 de Momentos permanece aberta e não foi integrada
**WHAT IS PROVED:** Recorrência polinomial sem divisão, identidade exata com `sigmaPadeD` original, transporte racional por caixas e sinais dos menores estão compilados em Lean. O3 prova os dois padrões de sinais condicionalmente à inclusão dos coeficientes nas caixas. PR #171 integrou a aproximação Euler da Gamma original por expressão finita com erro `10⁻³²` no domínio C2.
**WHAT IS CONDITIONAL:** `sigmaPadeD_signs_at_99_2000_of_source_boxes` e `sigmaPadeD_signs_at_1_10_of_source_boxes` exigem hipóteses explícitas de inclusão. A prova de que a fonte satisfaz essas hipóteses segue aberta.
**WHAT IS OPEN:** O4 ainda não prova as inclusões das caixas da fonte. A Gamma está a erro `10⁻³²` da expressão finita Euler, mas essa expressão ainda não tem caixas racionais estreitas.
**NEXT ACTION:** Derivar os coeficientes Taylor racionais de `gammaFinite 512 81 z` em torno do centro `z₀=(1/2+d)/2`, propagar as caixas pelo polinômio e fechar um limite uniforme para o resto no raio exterior `0.2`.
**EXACT NEXT MATHEMATICAL OBLIGATION:** Provar uma caixa para `Complex.Gamma z` nos discos Cauchy de raios `0.15` e `0.2`, usando `gamma_finite_512_error` mais a expansão Taylor; depois compor Hurwitz e a extração Cauchy/Fourier.
**EXACT NEXT COMMAND:** Ler `SigmaGammaEulerIntegral.lean` e implementar a expansão racional de `gammaFinite 512 81` em torno de `z₀=1099/4000` (`d=99/2000`), começando pelo limite de resto no raio `1/5`.
**DO NOT REPEAT:**
- Não refazer C2 eventual, C3, nem a recorrência analítica C4.
- Não redefinir `completedSigmaLogJet`, `sigmaPadeD` ou `completedSigmaDisplacedSourceCoefficient`.
- Não tratar caixas JSON nem saída de `mpmath.iv` como prova de inclusão.
- Não repetir as três gerações intervalares já reproduzidas salvo mudança no código, backend ou limites; os logs estão em `evidence/interval-certificate/`.
- Não usar aproximações de dois/três polos como substituto da fonte C2 completa.
- Não mesclar a PR #2 inteira sem auditar seu escopo.
- Não tocar nos logs/caches não rastreados das demais worktrees.

Detalhes de retomada, pins e estado atual: `SESSION_STATE.md`, `THEOREM_MAP.md`, `OPEN_OBLIGATIONS.md`, `CHECKPOINTS.md` e `evidence/rational-boxes/VALIDATION.md` neste diretório.
