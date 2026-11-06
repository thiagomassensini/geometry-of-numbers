# Checkpoint WIP — limite do peso de grau um

**Data:** 2026-11-06  
**Status:** INCOMPLETO; não usar como prova validada.

## Base, branch e pins

- Repositório: `geometry-of-numbers`.
- `origin/main` confirmado por `git ls-remote`: `c736dc073091e6184dbb673b622b6b91759accac` (PR #183).
- Branch de trabalho: `codex/c5-degree1-weight-bound-20261106`.
- Snapshot incompleto: commit `4d1b066`, publicado no GitHub para retomada; continua sem validação integral.
- Toolchain: `leanprover/lean4:v4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`, checkout `/home/thlinux/worktrees/carry-sigma-c2-pinned-045369`.
- Checkout de referência geometry: `/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105`.
- Hash atual do módulo WIP `SigmaRationalInterpolation.lean`: `1c4106c3d625ab21cda914428b62cfd080b872e3f79445f2e3ba6e48ef9aea6e`.
- Hash atual do checker fail-closed: `848e6b6cbdece12501f6553b1ffc16611c0e9e8a22368d80364240ae4282f0e4`.
- Não existe hash de `.olean` de produção: nenhum build completo foi concluído.

Os pins históricos de fonte, toolchain, Mathlib e Carry permanecem em `pins-and-sha256.txt`.

## Trabalho feito

Em `SigmaRationalInterpolation.lean`, foi adicionada uma rota simbólica para limitar o coeficiente linear das bases de Lagrange pelos produtos de diferenças quadradas e fatoriais. A versão anterior usava `native_decide`; ela foi rejeitada por introduzir axiomas próprios. O código atual não contém `native_decide`, `sorry`, `admit` nem axioma declarado, mas ainda não foi validado por compilação integral.

A cota da soma de inversos quadrados foi simplificada para `≤ 2`, suficiente para o limite do coeficiente de grau zero usado nessa rota. O lema auxiliar equivalente foi copiado para `c5-sum-bound-isolated.lean` e compilado isoladamente em Lean 4.32, com `BUILD_EXIT=0`. Esse teste não valida o módulo de produção nem os teoremas de pesos.

O checker `check_c5_interpolation_axioms.py` e `interpolation-audit.lean` foram ampliados para exigir sete raízes novas. A saída de auditoria que capturava os axiomas indevidos de `native_decide` foi preservada em `interpolation-audit-degree1-native-decide-rejected.log`. Os arquivos `interpolation-audit.log` e `interpolation-audit-check.log` foram restaurados ao relatório histórico aceito de 14 raízes da versão já integrada; esse resultado histórico não cobre as raízes novas.

## Resultado de compilação mais recente

O build integral mais recente é `c5-interpolation-degree1-pseries-retry9-build.log`. Lean 4.32 permaneceu em CPU contínua por 15m20s, com cerca de 2.9 GiB RSS, sem diagnóstico e sem `SigmaRationalInterpolation.olean`; a execução foi interrompida para investigação.

O perfil mais recente, `c5-interpolation-degree1-profile100-retry9-build.log`, mostra a elaboração de `c5_inv_sq_sum_range_le` concluída. Não foi observado erro nessa prova. O módulo completo continua sem conclusão após os lemas seguintes de produtos. Tentativas anteriores, incluindo os erros de tipo efetivamente encontrados e corrigidos, estão nos arquivos `c5-interpolation-degree1-*.log*`.

O limite de memória não é a causa observada: a última leitura registrou cerca de 63 GiB de `MemAvailable`; os processos Lean observados usaram menos de 3 GiB RSS e CPU contínua.

## Próximo passo exato

1. Instrumentar e separar os lemas imediatamente posteriores à cota da soma: `c5_rat_shifted_product`, `c5_shifted_product_erase` e `c5_abs_square_difference_product`.
2. Corrigir qualquer diagnóstico real preservando a prova simbólica, sem reintroduzir `native_decide`.
3. Compilar `SigmaRationalInterpolation` em diretório novo, com `warningAsError=true`.
4. Só após o build integral, recompilar `interpolation-audit.lean` e executar `check_c5_interpolation_axioms.py`; os sete teoremas adicionados devem mostrar somente `propext`, `Classical.choice` e `Quot.sound`.
5. Registrar source/olean hashes e então publicar uma PR pequena. Até lá, não afirmar que o limite de grau um está provado.

### Comando de build limpo

Executar da raiz do checkout C5, usando novo sufixo para `C5_OUTPUT` e novo nome para o log:

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

### Comando de auditoria após build integral

```bash
C5_EVIDENCE=$PWD/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes
C5_SOURCE_ROOT=$PWD/research/native-moving-schur-sigma
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_OUTPUT=$PWD/.lake/build/research/native-moving-schur-sigma/c5-degree1-resume-clean-20261106
C5_LEAN_BIN=$(cd "$C5_REFERENCE_ROOT" && elan which lean)
C5_MATHLIB_PATH=$(cd "$C5_REFERENCE_ROOT" && lake env printenv LEAN_PATH)
export LEAN_PATH="$C5_OUTPUT:$C5_SOURCE_ROOT:$C5_REFERENCE_ROOT/.lake/build/lib/lean:$C5_MATHLIB_PATH"
"$C5_LEAN_BIN" -DwarningAsError=true --root="$C5_EVIDENCE" \
  -o "$C5_OUTPUT/interpolation-audit.olean" \
  "$C5_EVIDENCE/interpolation-audit.lean" \
  > "$C5_EVIDENCE/interpolation-audit-degree1.log" 2>&1
python3 "$C5_SOURCE_ROOT/check_c5_interpolation_axioms.py" \
  "$C5_EVIDENCE/interpolation-audit-degree1.log" \
  > "$C5_EVIDENCE/interpolation-audit-degree1-check.log"
```

The isolated diagnostic command and its `BUILD_EXIT=0` result are recorded in
`c5-sum-bound-isolated-build.log`. It is not a production module build.
