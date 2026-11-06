# Retomar primeiro — C5

**MISSÃO:** C5 — certificação finita da primeira janela negativa C2 original

**FASE ATUAL:** O3 integrada; O4 em andamento, origem das caixas ainda aberta

**SUBTAREFA ATUAL:** formalizar limites dos pesos de Lagrange nos 129 nós racionais; depois certificar a cota analítica da fonte e os valores racionais necessários

**ÚLTIMA PROVA PUBLICADA:** PR #177, identidade algébrica de interpolação em 129 nós, merge `0702371cff0c6016eae9eaa0aa9331ae95483456`

**REGISTRO DE ESTADO ANTERIOR À PR #177:** PR #176, merge `ac84c9302ae608e39c742f856ad361921653f268`

**ÚLTIMO CHECKPOINT DE ESTADO:** PR #178, merge `7ad7e29195790eedda01645e71e5c52edf1b4e6b`

**MAIN após PR #178:** `7ad7e29195790eedda01645e71e5c52edf1b4e6b`

**BRANCH C5:** `codex/c5-finite-c2-certification-20261106`, último commit remoto `476df788ab3cdb0deb28d67ec426c559341e3f05`

**C5 PRs:** #165–#178 estão integradas; a PR #2 de Momentos permanece aberta e não foi integrada.

## Estado matemático

**PROVADO:** a recorrência polinomial sem divisão, a identidade exata com `sigmaPadeD` original, os sinais condicionais de O3 e a aproximação Euler-Gamma com erro `10⁻²⁵⁹` estão compilados em Lean 4.32. A identidade de Lagrange em 129 nós recupera exatamente polinômios racionais de grau menor que 129. A soma absoluta dos pesos escalados para o coeficiente de grau zero é exatamente `1`.

**CONDICIONAL:** os padrões de sinais finais em `d=99/2000` e `d=1/10` ainda dependem de `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.

**ABERTO:** os limites numéricos das somas absolutas dos pesos escalados para os graus `1≤n≤14`, a cota analítica `|completedSigmaDensity d t| ≤ 10^100` no disco de raio `2/5`, e a avaliação rigorosa da fonte nos 129 pontos ainda não estão provados no Lean. Portanto, O4 segue aberta e nenhum teorema incondicional de janela C5 foi declarado.

## Próximas ações

1. Provar limites racionais exatos para `c5InterpolationWeightSum n` nos graus `1≤n≤14`, conferindo os limites exploratórios em `evidence/rational-boxes/rational-interpolation-analysis.log`.
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
