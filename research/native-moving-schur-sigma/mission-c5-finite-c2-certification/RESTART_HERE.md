# Retomar primeiro — missão C5

**MISSÃO:** certificar a primeira janela negativa da fonte C2 original, para `d=99/2000` e `d=1/10`.

## Estado do checkpoint atual — 2026-11-06

- **Fase:** O4, origem das caixas racionais ainda aberta.
- **Subtarefa recém-validada:** limite racional simbólico da soma absoluta dos pesos escalados de interpolação de grau um.
- **Subtarefa validada:** limite racional simbólico da soma absoluta dos pesos escalados de grau um.
- **Lean:** `leanprover/lean4:v4.32.0`; Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`; Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- **Build limpo:** `evidence/rational-boxes/c5-interpolation-degree1-final-clean-build.log`, `BUILD_EXIT=0`.
- **Auditoria:** 21 raízes; apenas `propext`, `Classical.choice`, `Quot.sound`. Ver `interpolation-audit-degree1-final-clean.log` e `interpolation-audit-degree1-final-clean-check.log`.
- **Hashes:** `evidence/rational-boxes/c5-interpolation-degree1-final-clean-source-olean-sha256.txt`.
- **Último teorema verificado:** `CarrySigmaObstruction.c5InterpolationWeightSum_one_lt_ten_eleven`.
- **Último arquivo compilado:** `research/native-moving-schur-sigma/SigmaRationalInterpolation.lean`.
- **Último commit de prova:** `90a208df98e74a7c5ab1fe83a9ef0fc90c3d3cb6`; PR #185, merge `c840ba35711ac8f938fa24c191f2af60f505480d`.
- **Último SHA remoto da branch de prova:** `90a208df98e74a7c5ab1fe83a9ef0fc90c3d3cb6`.
- **Checkpoint incompleto:** PR #184, merge `5528ddc8093a22682c87f3f9c6575e30e90a7011`; logs e tentativas continuam preservados como histórico.
- **Main geometry após a prova:** `c840ba35711ac8f938fa24c191f2af60f505480d`.
- **PR de prova aberta:** nenhuma. Confira PRs documentais no GitHub ao retomar.

## O que está provado, condicional e aberto

- **Provado em Lean:** para grau um, cada peso de base satisfaz a cota usada no módulo; `c5InterpolationCoeffOneAbsSum_le_six` e `c5InterpolationWeightSum_one_lt_ten_eleven` dão a soma escalada `<10^11`.
- **Provado condicionalmente:** os padrões de sinais da primeira janela negativa para os dois deslocamentos, assumindo que os coeficientes originais pertencem às caixas racionais O3.
- **Ainda aberto:** limites dos pesos para graus `2..14`; cota analítica da densidade no disco de raio `2/5`; avaliações racionais da fonte nos 129 pontos; inclusão dos coeficientes originais nas caixas; teoremas finais incondicionais.
- **Não há bloqueio na matemática de O3.** O bloqueio para a certificação completa é a inclusão rigorosa das caixas da fonte C2 original; a saída `mpmath.iv` permanece evidência computacional, não prova formal.

## Próxima obrigação matemática

Generalizar a estimativa dos coeficientes das bases de Lagrange para grau `2..14`. Uma rota a avaliar é fatorar, para `j>0`, a base como o coeficiente de grau um vezes `x` vezes um produto de fatores `1 - x/k²`, e limitar os coeficientes por somas simétricas elementares; tratar `j=0` pelo produto `∏(1-x/k²)`. Usar uma cota uniforme suficientemente grande se ela ainda mantiver a margem de precisão da ponte Gamma `10⁻²⁵⁹`; não é necessário reproduzir o limite exploratório `10^124` se uma cota mais simples servir.

## Ficha obrigatória de retomada

- **CURRENT PHASE:** O4, limites dos pesos e inclusão das caixas da fonte ainda incompletos.
- **CURRENT SUBTASK:** provar limites Lean para os pesos escalados de graus `2..14`.
- **LAST VERIFIED THEOREM:** `CarrySigmaObstruction.c5InterpolationWeightSum_one_lt_ten_eleven`.
- **LAST COMPILED FILE:** `SigmaRationalInterpolation.lean`.
- **LAST SUCCESSFUL COMMIT:** `90a208df98e74a7c5ab1fe83a9ef0fc90c3d3cb6`, integrado por #185 em `c840ba35711ac8f938fa24c191f2af60f505480d`.
- **LAST REMOTE SHA:** `origin/codex/c5-degree1-weight-bound-pr-20261106` = `90a208df98e74a7c5ab1fe83a9ef0fc90c3d3cb6`.
- **CURRENT BRANCH:** a prova está integrada; inicie trabalho matemático em uma branch nova da `origin/main` atual. Este registro é posterior à PR #185.
- **MAIN SHA:** `c840ba35711ac8f938fa24c191f2af60f505480d` na confirmação da prova #185; atualize com `git fetch` ao retomar.
- **OPEN PR:** nenhuma PR matemática; consulte o GitHub para PRs documentais.
- **WHAT IS PROVED:** limite de grau um `<10^11`, soma absoluta das bases `≤6`, build limpo e auditoria de 21 raízes.
- **WHAT IS CONDITIONAL:** sinais O3 dos menores originais, condicionados às inclusões dos coeficientes nas caixas.
- **WHAT IS BLOCKED:** inclusão rigorosa da fonte nas caixas; faltam também limites de peso de graus `2..14` e os subpassos analíticos da fonte.
- **EXACT NEXT COMMAND:** `git fetch origin --prune && git worktree add -b codex/c5-weight-degree-2-14-20261106 /home/thlinux/worktrees/geometry-of-numbers-c5-weight-degree-2-14-20261106 origin/main`.
- **EXACT NEXT MATHEMATICAL OBLIGATION:** limitar os coeficientes de graus `2..14` das bases de Lagrange sem expansão direta gigantesca; depois fechar a cota analítica e as inclusões C2.

## Comando de build/auditoria após a próxima alteração Lean

Da raiz da worktree C5, após editar `SigmaRationalInterpolation.lean`, use um diretório de saída novo:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-next-clean-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_REFERENCE_ROOT/.lake/build/lib/lean:$C5_MATHLIB_PATH"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT" SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaRationalInterpolation \
  > "$C5_EVIDENCE/c5-next-clean-build.log" 2>&1
```

Depois compile `interpolation-audit.lean` com a mesma `LEAN_PATH`, atualize o checker para as raízes novas e execute `check_c5_interpolation_axioms.py`. Grave hashes da fonte, `.olean` e log antes de publicar.

## DO NOT REPEAT

- Não refazer C0–C4 nem O2/O3: estão integrados e os sinais C5 continuam condicionais às caixas.
- Não refazer `c5LagrangeBasisProductCoeffOne_bound`, `c5InterpolationCoeffOneAbsSum_le_six` ou `c5InterpolationWeightSum_one_lt_ten_eleven`; build limpo e auditoria de 21 raízes estão registrados.
- Não reutilizar a tentativa com `native_decide`; ela introduziu `_native.native_decide` e foi rejeitada.
- Não declarar as caixas JSON como inclusões dos coeficientes originais sem prova.
- Não alterar a PR #2 de Momentos nem mesclá-la sem auditoria de escopo.
- Preservar caches, logs e alterações não rastreados nas outras worktrees.
