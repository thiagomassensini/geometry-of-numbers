# C5 — limite de grau um dos pesos de interpolação

**Status:** prova Lean compilada e auditada em uma saída limpa.

O módulo `SigmaRationalInterpolation.lean` prova:

- `c5LagrangeBasisProductCoeffOne_bound`: para cada base não constante, a magnitude do coeficiente linear é limitada por `2/j^2`;
- `c5InterpolationCoeffOneAbsSum_le_six`: a soma das magnitudes dos coeficientes lineares das 129 bases é no máximo `6`;
- `c5InterpolationWeightSum_one_lt_ten_eleven`: após a escala dos nós `t_j=j/100000`, a soma absoluta do peso de grau um é estritamente menor que `10^11`.

As cotas seguem de identidades finitas de produtos fatoriais, da desigualdade central dos fatoriais e da cota racional `sum_{k<n} 1/(k+1)^2 ≤ 2`. A tentativa por expansão bruta e a tentativa anterior com `native_decide` permanecem arquivadas; esta prova simbólica não depende de decisão nativa.

## Validação reproduzível

- Lean `leanprover/lean4:v4.32.0`.
- Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Referência Geometry: `caa07002306b555fea5624cc11ab2ea5811a4324`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Build limpo em `c5-degree1-final-clean-20261106`, com `warningAsError=true`: `c5-interpolation-degree1-final-clean-build.log`, `BUILD_EXIT=0`.
- Auditoria transitiva das 21 raízes em `interpolation-audit-degree1-final-clean.log`; o checker fail-closed aceitou todas em `interpolation-audit-degree1-final-clean-check.log`.
- As três novas raízes de limites aparecem explicitamente na saída de `#print axioms`. Todas as 21 dependem apenas de `propext`, `Classical.choice` e `Quot.sound`.
- Hashes SHA-256 da fonte e dos dois `.olean` limpos: `c5-interpolation-degree1-final-clean-source-olean-sha256.txt`.
- `SigmaRationalInterpolation.lean` não contém `sorry`, `admit`, axiomas declarados nem `native_decide`.

Reprodução exata, a partir da worktree C5:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-degree1-final-clean-20261106
C5_EVIDENCE=$C5_SOURCE_ROOT/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
mkdir -p "$C5_OUTPUT"
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_REFERENCE_ROOT/.lake/build/lib/lean:$C5_MATHLIB_PATH"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT" SIGMA_OUTPUT_DIR="$C5_OUTPUT" LEAN_BIN="$C5_LEAN_BIN"
if bash "$C5_SOURCE_ROOT/compile_sigma_pade.sh" SigmaRationalInterpolation \
    > "$C5_EVIDENCE/c5-interpolation-degree1-final-clean-build.log" 2>&1; then
  printf 'BUILD_EXIT=0\n' >> "$C5_EVIDENCE/c5-interpolation-degree1-final-clean-build.log"
else
  status=$?
  printf 'BUILD_EXIT=%s\n' "$status" >> "$C5_EVIDENCE/c5-interpolation-degree1-final-clean-build.log"
  exit "$status"
fi

"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_EVIDENCE" \
  -o "$C5_OUTPUT/interpolation-audit.olean" \
  "$C5_EVIDENCE/interpolation-audit.lean" \
  > "$C5_EVIDENCE/interpolation-audit-degree1-final-clean.log" 2>&1
python3 "$C5_SOURCE_ROOT/check_c5_interpolation_axioms.py" \
  "$C5_EVIDENCE/interpolation-audit-degree1-final-clean.log" \
  > "$C5_EVIDENCE/interpolation-audit-degree1-final-clean-check.log"
sha256sum "$C5_SOURCE_ROOT/SigmaRationalInterpolation.lean" \
  "$C5_OUTPUT/SigmaRationalInterpolation.olean" \
  "$C5_OUTPUT/interpolation-audit.olean" \
  > "$C5_EVIDENCE/c5-interpolation-degree1-final-clean-source-olean-sha256.txt"
```

As tentativas intermediárias que produziram diagnósticos estão preservadas
byte a byte após descompressão em `c5-interpolation-degree1-fixed-build.log.gz`,
`c5-interpolation-degree1-fixed-build2.log.gz` e
`c5-interpolation-degree1-fixed-build3.log.gz`. O checkpoint histórico registra
as tentativas anteriores e os comandos de retomada.

## Limites do resultado

Esta etapa cobre somente o coeficiente de grau um. Os pesos de graus `2..14`, a cota analítica da densidade, as avaliações nos 129 pontos e a inclusão dos coeficientes da fonte C2 nas caixas ainda estão abertos. Os teoremas O3 e os sinais das janelas permanecem condicionais às caixas; esta prova não certifica incondicionalmente os menores originais.
