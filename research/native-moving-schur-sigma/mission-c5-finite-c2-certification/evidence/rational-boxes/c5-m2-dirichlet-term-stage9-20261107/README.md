# C5 — termo nodal `m=2`, transição Taylor `n=8→9` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage9Certificate.lean` prova
`c5RoundedExpStateC_stage9_correct`. O passo certifica o produto de um
intervalo não-negativo pelo argumento não-positivo, o termo de coeficiente
`1/8! = 1/40320`, o arredondamento em 896 bits e a atualização da soma por
aritmética racional.

O build Lean 4.32.0 com `warningAsError=true` passou contra Geometry no pin
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry no pin
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O log registra `BUILD_EXIT=0`.
As cinco declarações auditadas usam somente `propext`, `Classical.choice` e
`Quot.sound`; não há `sorryAx`. SHA-256 do `.olean`:
`552f645e61e473abfce92548c01bca31367382a9553d1686725f0570680cda5d`.

`SigmaC5M2TaylorStateStage9ExportProbe.lean` exporta os extremos racionais
usados na fonte do certificado. A saída `#eval` é dado de construção, não
prova; o arquivo de certificado verifica as igualdades da recorrência no Lean.
As duas fontes e os logs estão preservados neste diretório.

O escopo é somente a recorrência Taylor até `n=9` de um nó. Não prova
`n=10…192`, outros nós, quadraturas, caixa completa, ponte CSV–Lean, inclusão
dos coeficientes originais da fonte C2 ou sinais finais. C5 permanece
incompleta. Próximo estado: `n=10`.

## Pins e ambiente

- Base da `main`: `27c5496a55dd3bbf2fbca5b7fe92371f7ab44662` (PR #256).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` durante a compilação: `63338792 kB`.
- SHA-256 da fonte de prova: `ae902249b165a41db0c2a3a92f59b5f60320cdcd22f9f2e7d704c5ccc4089ac0`.
- SHA-256 do probe: `1d2fb1451183a4d81af4e0cb1c49209fc1379cd711d8bd11d930e2bb0f37bfc6`.

## Reprodução

Compile os estados integrados até `n=8` conforme
`../c5-m2-dirichlet-term-stage8-20261107/README.md` e preserve o output
compartilhado `.cache/c5-m2-term`. Na raiz da worktree:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage9ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage9Certificate
```

`state-stage9-export-probe.log` registra os extremos exportados;
`state-stage9-build.log` registra build e auditoria. Os checksums estão em
`SHA256SUMS.txt`.

## Publicação

Este checkpoint está local, sem PR ou merge. É parcial e não conclui C5.
