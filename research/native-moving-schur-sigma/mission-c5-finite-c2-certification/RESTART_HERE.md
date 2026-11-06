# Retomar primeiro — C5

**MISSÃO:** C5 — certificação finita da primeira janela negativa C2 original
**CURRENT PHASE:** O3 integrada; O4 em investigação (inclusão da fonte original nas caixas)
**CURRENT SUBTASK:** Certificar os 129 valores racionais de `completedSigmaDensity` e formalizar a interpolação que recupera `c₀..c₁₄`; depois compor a rota à fonte C2 original
**LAST VERIFIED THEOREMS:** `sigmaPadeD_signs_at_99_2000_of_source_boxes` e `sigmaPadeD_signs_at_1_10_of_source_boxes`
**LAST COMPILED FILE:** `SigmaGammaEulerIntegral.lean` e `gamma-euler-audit.lean` (Lean 4.32; erro uniforme `10⁻²⁵⁹`; doze raízes auditadas)
**LAST SUCCESSFUL MERGE:** PR #174, atualização pós-#173, merge `47a28db231dfbae24cbf1238084a60cf1b8206fb`
**LAST REMOTE SHA:** `origin/main=47a28db231dfbae24cbf1238084a60cf1b8206fb`; Momentos `origin/research/sigma-pade-dimension-depth-20261104=68c9b5f0a196289e28a8e5586146707d27df6b75`
**CURRENT BRANCH:** `codex/c5-finite-c2-certification-20261106`
**MAIN SHA:** `47a28db231dfbae24cbf1238084a60cf1b8206fb`
**C5 PRs:** #165–#174 estão integradas; a PR #2 de Momentos permanece aberta e não foi integrada
**WHAT IS PROVED:** Recorrência polinomial sem divisão, identidade exata com `sigmaPadeD` original, transporte racional por caixas e sinais dos menores estão compilados em Lean. O3 prova os dois padrões de sinais condicionalmente à inclusão dos coeficientes nas caixas. PR #171 integrou a ponte Euler-Gamma a erro `10⁻³²`; PR #173 melhora o erro para `10⁻⁹⁹`; `gamma_finite_3072_620_error` reduz o erro a `10⁻²⁵⁹` nesta branch.
**WHAT IS CONDITIONAL:** `sigmaPadeD_signs_at_99_2000_of_source_boxes` e `sigmaPadeD_signs_at_1_10_of_source_boxes` exigem hipóteses explícitas de inclusão. A prova de que a fonte satisfaz essas hipóteses segue aberta.
**WHAT IS OPEN:** O4 ainda não prova as inclusões das caixas da fonte. A ponte Euler está a erro `10⁻²⁵⁹`, mas `gammaFinite 3072 620` ainda não foi avaliada em caixas racionais nos valores necessários.
**NEXT ACTION:** Formalizar a interpolação racional em `t_j=j/100000`, `0≤j≤128`, para recuperar os coeficientes pares `c₀..c₁₄` da fonte C2; em paralelo, certificar o avaliador da fonte nos pontos racionais.
**EXACT NEXT MATHEMATICAL OBLIGATION:** Provar formalmente que a interpolação de 129 pontos recupera os coeficientes até o erro requerido, usando uma cota analítica uniforme na circunferência de raio `2/5`; depois certificar `completedSigmaDensity` em cada ponto racional sem trocar a fonte original.
**EXACT NEXT COMMAND:** Reproduzir `analyze_rational_interpolation.py`; em seguida definir em Lean os pesos racionais de Lagrange e provar os limites exatos indicados em `evidence/rational-boxes/rational-interpolation-analysis.log`.
**DO NOT REPEAT:**
- Não refazer C2 eventual, C3, nem a recorrência analítica C4.
- Não redefinir `completedSigmaLogJet`, `sigmaPadeD` ou `completedSigmaDisplacedSourceCoefficient`.
- Não tratar caixas JSON nem saída de `mpmath.iv` como prova de inclusão.
- Não repetir as três gerações intervalares já reproduzidas salvo mudança no código, backend ou limites; os logs estão em `evidence/interval-certificate/`.
- Não usar aproximações de dois/três polos como substituto da fonte C2 completa.
- Não mesclar a PR #2 inteira sem auditar seu escopo.
- Não tocar nos logs/caches não rastreados das demais worktrees.

Detalhes de retomada, pins e estado atual: `SESSION_STATE.md`, `THEOREM_MAP.md`, `OPEN_OBLIGATIONS.md`, `CHECKPOINTS.md` e `evidence/rational-boxes/VALIDATION.md` neste diretório.
