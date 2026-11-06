# Retomar primeiro — C5

**MISSÃO:** C5 — certificação finita da primeira janela negativa C2 original

**FASE ATUAL:** O3 integrada; O4 em andamento, origem das caixas ainda aberta

**SUBTAREFA ATUAL:** formalizar limites dos pesos de Lagrange nos 129 nós racionais; depois certificar a cota analítica da fonte e os valores racionais necessários

**ÚLTIMA PROVA PUBLICADA:** PR #177, identidade algébrica de interpolação em 129 nós, merge `0702371cff0c6016eae9eaa0aa9331ae95483456`

**ÚLTIMO REGISTRO DE ESTADO:** PR #176, merge `ac84c9302ae608e39c742f856ad361921653f268`

**MAIN após a PR #177:** `0702371cff0c6016eae9eaa0aa9331ae95483456`

**BRANCH C5:** `codex/c5-finite-c2-certification-20261106`, commit de prova remoto `67ff0b7ef32de922dda7cd0fcea890bc3afbf738`

**C5 PRs:** #165–#177 estão integradas; a PR #2 de Momentos permanece aberta e não foi integrada.

## Estado matemático

**PROVADO:** a recorrência polinomial sem divisão, a identidade exata com `sigmaPadeD` original, os sinais condicionais de O3 e a aproximação Euler-Gamma com erro `10⁻²⁵⁹` estão compilados em Lean 4.32. A identidade de Lagrange em 129 nós também está provada: todo polinômio racional de grau menor que 129 é recuperado exatamente por suas avaliações nos nós `j²`, e seus coeficientes são a soma ponderada pelos coeficientes das bases de Lagrange.

**CONDICIONAL:** os padrões de sinais finais em `d=99/2000` e `d=1/10` ainda dependem de `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.

**ABERTO:** não estão provados no Lean os limites numéricos das somas absolutas dos pesos escalados, a cota analítica `|completedSigmaDensity d t| ≤ 10^100` no disco de raio `2/5`, nem a avaliação rigorosa da fonte nos 129 pontos. Portanto, O4 segue aberta e nenhum teorema incondicional de janela C5 foi declarado.

## Próximas ações

1. Provar limites racionais exatos para `c5InterpolationWeightSum n` nos graus `n≤14`, conferindo os limites exploratórios em `evidence/rational-boxes/rational-interpolation-analysis.log`.
2. Provar uma cota uniforme da extensão analítica da densidade no disco de raio `2/5`.
3. Certificar as avaliações racionais da fonte mantendo a cabeça C2, a cauda exponencial exata e a completação original; compor então com Hurwitz/Cauchy e as caixas O3.

Build Lean 4.32 e auditoria de axiomas da identidade algébrica estão em `evidence/rational-boxes/c5-interpolation-build.log`, `interpolation-audit.log` e `interpolation-audit-check.log`. O módulo novo é `research/native-moving-schur-sigma/SigmaRationalInterpolation.lean`; os comandos reproduzíveis estão em `evidence/rational-boxes/VALIDATION.md`.

## Não repetir

- Não refazer C0, C1, C1B, C2 eventual, C3 ou C4.
- Não redefinir `completedSigmaLogJet`, `sigmaPadeD` ou `completedSigmaDisplacedSourceCoefficient`.
- Não tratar JSONs nem saída de `mpmath.iv` como prova de inclusão.
- Não substituir a fonte C2 completa por aproximações de dois ou três polos.
- Não mesclar a PR #2 de Momentos inteira sem auditar seu escopo.
- Não tocar nos logs e caches não rastreados das outras worktrees.
