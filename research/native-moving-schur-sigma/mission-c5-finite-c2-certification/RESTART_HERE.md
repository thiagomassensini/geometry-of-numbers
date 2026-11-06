# Retomar primeiro — C5

**MISSÃO:** C5 — certificação finita da primeira janela negativa C2 original

**FASE ATUAL:** O3 integrada; O4 em andamento, origem das caixas ainda aberta

**SUBTAREFA ATUAL:** formalizar limites dos pesos de Lagrange nos 129 nós racionais; depois certificar a cota analítica da fonte e os valores racionais necessários

**ÚLTIMA PROVA PUBLICADA:** PR #181, estrutura derivativa para o coeficiente linear, merge `7460497307e7ed0ffb47ef1ac96b096e9b410472`

**ÚLTIMO CHECKPOINT DE ESTADO:** PR #182, estado pós-PR #181, merge `8f8b9da2b8c1e8f3b8d1290608c8b2abffe9c285`

**MAIN após PR #181:** `7460497307e7ed0ffb47ef1ac96b096e9b410472`

**CHECKPOINT DE ESTADO após PR #181:** `8f8b9da2b8c1e8f3b8d1290608c8b2abffe9c285`

**BRANCH C5:** a branch de prova foi removida após o merge da PR #181. Abrir uma branch nova a partir da `main` `7460497307e7ed0ffb47ef1ac96b096e9b410472`.

**C5 PRs:** #165–#181 estão integradas; a PR #2 de Momentos permanece aberta e não foi integrada.

## Estado matemático

**PROVADO:** a recorrência polinomial sem divisão, a identidade exata com `sigmaPadeD` original, os sinais condicionais de O3 e a aproximação Euler-Gamma com erro `10⁻²⁵⁹` estão compilados em Lean 4.32. A identidade de Lagrange em 129 nós recupera exatamente polinômios racionais de grau menor que 129. A soma absoluta dos pesos escalados para grau zero é exatamente `1`; para grau um, o coeficiente de cada base está expresso como a derivada avaliada em zero.

**CONDICIONAL:** os padrões de sinais finais em `d=99/2000` e `d=1/10` ainda dependem de `sigmaC00495SourceBoxes` e `sigmaC01SourceBoxes`.

**ABERTO:** os limites numéricos das somas absolutas dos pesos escalados para os graus `1≤n≤14`, a cota analítica `|completedSigmaDensity d t| ≤ 10^100` no disco de raio `2/5`, e a avaliação rigorosa da fonte nos 129 pontos ainda não estão provados no Lean. Portanto, O4 segue aberta e nenhum teorema incondicional de janela C5 foi declarado.

## Próximas ações

1. Provar limites racionais exatos para `c5InterpolationWeightSum n` nos graus `1≤n≤14`. Para grau um, usar a fórmula de derivada e evitar expandir as 129 bases de uma vez; a tentativa custosa e seu erro estão em `evidence/rational-boxes/interpolation-weight-degree1-prototype.log`.
2. Provar uma cota uniforme da extensão analítica da densidade no disco de raio `2/5`.
3. Certificar as avaliações racionais da fonte mantendo a cabeça C2, a cauda exponencial exata e a completação original; compor então com Hurwitz/Cauchy e as caixas O3.

Build Lean 4.32 e auditoria de axiomas da identidade algébrica estão em `evidence/rational-boxes/c5-interpolation-build.log`, `interpolation-audit.log` e `interpolation-audit-check.log`. O módulo é `research/native-moving-schur-sigma/SigmaRationalInterpolation.lean`; os comandos reproduzíveis estão em `evidence/rational-boxes/VALIDATION.md`.

A etapa de grau um foi integrada pela PR #181. O checkpoint e o erro da tentativa numérica estão preservados em `evidence/rational-boxes/`; o limite de peso ainda está aberto.

## Não repetir

- Não refazer C0, C1, C1B, C2 eventual, C3 ou C4.
- Não redefinir `completedSigmaLogJet`, `sigmaPadeD` ou `completedSigmaDisplacedSourceCoefficient`.
- Não tratar JSONs nem saída de `mpmath.iv` como prova de inclusão.
- Não substituir a fonte C2 completa por aproximações de dois ou três polos.
- Não mesclar a PR #2 de Momentos inteira sem auditar seu escopo.
- Não tocar nos logs e caches não rastreados das outras worktrees.
