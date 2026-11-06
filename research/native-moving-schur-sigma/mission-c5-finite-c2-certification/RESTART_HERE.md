# Retomar primeiro — missão C5

**MISSÃO:** certificar as primeiras janelas negativas da fonte C2 original,
para `d=99/2000` e `d=1/10`. A validação segue incompleta até que as caixas
racionais contenham os coeficientes originais.

## Estado atual — 2026-11-06

- C1–C4 e O3 estão integradas. O3 prova os sinais finais apenas sob as
  hipóteses explícitas de inclusão nas caixas.
- Em Lean 4.32 estão provados os limites dos pesos escalados de graus `0..14`:
  grau zero `=1`, grau um `<10^11`, e todo `2≤n≤14` tem soma `<10^145`.
- `c5InterpolationWeightSum_lt_ten_145` é a última declaração validada.
- A PR #187 integrou essa prova: commit `6424f4334edd5c776997116403043635fa0c8f83`, merge na `main` `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
- Build limpo com `warningAsError=true`: `evidence/rational-boxes/c5-interpolation-degree2-14-final-clean-build.log`, `BUILD_EXIT=0`.
- Auditoria transitiva de 23 teoremas: somente `propext`, `Classical.choice` e
  `Quot.sound`. O checker fail-closed passou; logs e hashes estão ao lado.
- O estado atual foi retomado em `codex/c5-state-after-pr187-20261106`, sobre
  `origin/main` no merge `9f4a1b43cb2b155dfc55bf49ef77d1914210b796`.
- Pins: Lean `leanprover/lean4:v4.32.0`, Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`, Carry
  `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- C1B/C2/C3/C4 e provas C5 anteriores não devem ser refeitas. A PR #185
  integrou o limite de grau um no merge
  `c840ba35711ac8f938fa24c191f2af60f505480d`; #184 integrou o checkpoint
  explicitamente incompleto em `5528ddc8093a22682c87f3f9c6575e30e90a7011`.

## O que continua aberto

Falta provar uma cota analítica uniforme para `completedSigmaDensity d t` no
disco de raio `2/5`, certificar a avaliação racional da fonte nos 129 nós e
provar a inclusão dos coeficientes originais nas caixas O3. A saída `mpmath.iv`
continua sendo evidência computacional, não prova de inclusão. Não declarar os
teoremas finais incondicionais enquanto esse gate estiver aberto.

Preservar a fonte C2 original, a cabeça e a cauda exponencial exata. A ponte
Euler-Gamma de erro `10⁻²⁵⁹` está provada. A cota dos pesos `<10^145` é uniforme
e suficiente para a margem estimada; não é necessário recuperar o limite
exploratório `10^124`.

## Próximo passo

Continuar com a cota analítica da fonte C2 no disco de raio `2/5` e a
certificação nodal. PR #187 já integrou a prova de pesos; este documento
registra o merge real e mantém explícito o estado incompleto da missão.

## Comando de build e auditoria

Da raiz da worktree C5:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-degree2-14-final-clean-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_REFERENCE_ROOT/.lake/build/lib/lean:$C5_MATHLIB_PATH"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT" SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
if bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaRationalInterpolation \
    > "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-build.log" 2>&1; then
  printf 'BUILD_EXIT=0\n' >> "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-build.log"
else
  C5_STATUS=$?
  printf 'BUILD_EXIT=%s\n' "$C5_STATUS" >> "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-build.log"
  exit "$C5_STATUS"
fi
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_EVIDENCE" \
  -o "$C5_OUTPUT/interpolation-audit.olean" \
  "$C5_EVIDENCE/interpolation-audit.lean" \
  > "$C5_EVIDENCE/interpolation-audit-degree2-14-final-clean.log" 2>&1
python3 "$C5_SOURCE_ROOT/check_c5_interpolation_axioms.py" \
  "$C5_EVIDENCE/interpolation-audit-degree2-14-final-clean.log" \
  > "$C5_EVIDENCE/interpolation-audit-degree2-14-final-clean-check.log"
sha256sum "$C5_SOURCE_ROOT/SigmaRationalInterpolation.lean" \
  "$C5_OUTPUT/SigmaRationalInterpolation.olean" \
  "$C5_OUTPUT/interpolation-audit.olean" \
  > "$C5_EVIDENCE/c5-interpolation-degree2-14-final-clean-source-olean-sha256.txt"
```

The checker report and hashes already committed with the validation record are
`interpolation-audit-degree2-14-final-clean-check.log` and
`c5-interpolation-degree2-14-final-clean-source-olean-sha256.txt`.
