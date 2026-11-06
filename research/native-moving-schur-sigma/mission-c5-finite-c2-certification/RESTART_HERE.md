# Retomar primeiro — C5

## Checkpoint corrente — limite de grau um ainda não validado

**Base remota confirmada:** `origin/main` = `c736dc073091e6184dbb673b622b6b91759accac` (PR #183).
**Branch local:** `codex/c5-degree1-weight-bound-20261106`, baseada nessa revisão.
**Estado desta branch:** prova do limite de grau um em andamento; sem `.olean`
integral, sem auditoria nova aprovada, sem PR e sem merge. O checkpoint desta
etapa é explicitamente incompleto.

O arquivo de produção alterado é
`research/native-moving-schur-sigma/SigmaRationalInterpolation.lean`. Ele agora
contém uma tentativa simbólica de provar `c5LagrangeBasisProductCoeffOne_bound`
com produtos fatoriais, mas o build integral não terminou. O lema auxiliar
`c5_inv_sq_sum_range_le_isolated`, em
`evidence/rational-boxes/c5-sum-bound-isolated.lean`, compilou isoladamente
(`BUILD_EXIT=0`); isso não valida o arquivo de produção nem o limite final.

**Último build integral:** `c5-interpolation-degree1-pseries-retry9-build.log`,
interrompido após 15m20s sem diagnóstico e sem `.olean`. O perfil
`c5-interpolation-degree1-profile100-retry9-build.log` mostra a elaboração do
lema da soma concluída; os lemas de produto seguintes não chegaram a uma
conclusão observável. Tentativas, traces comprimidos e pins estão em
`evidence/rational-boxes/`.

Erros concretos anteriores e estado atual:

- A comparação `n*(n+1) ≤ (n+1)^2` não unificava `x*x` com `x^2`; a prova atual
  explicita o produto e fecha a igualdade por `ring`.
- `sum_Ico_eq_sum_range` foi colocado no sentido direto e agora simplifica
  `n+1-1` com `Nat.add_sub_cancel`.
- A cota de `sum_Ioo_inv_sq_le` agora reduz numericamente `2/(1+1)` a `1`.
- A versão anterior baseada em `native_decide` foi rejeitada pela auditoria por
  adicionar axiomas `_native.native_decide`. Sua saída está preservada em
  `interpolation-audit-degree1-native-decide-rejected.log`; não reutilizar essa
  prova. Os logs de auditoria aceitos para 14 raízes foram restaurados e são
  apenas históricos, relativos à versão integrada anterior.

**Próxima ação exata:** localizar o custo nos próximos lemas de produto,
começando por `c5_rat_shifted_product`, `c5_shifted_product_erase` e
`c5_abs_square_difference_product`. Não interpretar uma execução sem saída como
sucesso. Depois de uma revisão que conclua, compilar em diretório novo e executar
a auditoria das raízes novas antes de atualizar o status.

Comando-base de retomada (usar diretório de saída novo):

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-degree1-resume-clean-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_REFERENCE_ROOT/.lake/build/lib/lean:$C5_MATHLIB_PATH"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT" SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaRationalInterpolation \
  > "$C5_EVIDENCE/c5-interpolation-degree1-resume-build.log" 2>&1
```

Depois do build, executar a auditoria Lean e
`check_c5_interpolation_axioms.py` conforme
`evidence/rational-boxes/VALIDATION.md`. A auditoria histórica não satisfaz os
requisitos atualizados do checker.

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
