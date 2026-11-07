# C5 — termo nodal `m=2`, transição Taylor `n=7→8` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage8Certificate.lean` prova
`c5RoundedExpStateC_stage8_correct`. A transição verifica o produto de dois
intervalos não-positivos, o termo com coeficiente `1/7! = 1/5040`, seu
arredondamento em 896 bits e a atualização racional da soma.

A compilação passou em Lean 4.32.0 com `warningAsError=true`, contra Geometry
no pin `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry no pin
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O log registra `BUILD_EXIT=0`.
As cinco declarações auditadas dependem somente de `propext`,
`Classical.choice` e `Quot.sound`, sem `sorryAx`. O SHA-256 do `.olean` é
`c170303a33a8578bb493ba25e3ffb69b1b85f13fb7a4a73002f75275bc8e9545`.

`SigmaC5M2TaylorStateStage8ExportProbe.lean` exporta os extremos racionais
usados para compor o certificado. A saída de `#eval` é dado de trabalho; a
fonte de prova verifica no Lean as igualdades da recorrência por aritmética
racional. Fonte, logs, pins, hashes e comandos estão preservados aqui.

O alcance é apenas a recorrência Taylor até `n=8` de um nó. Não prova os
estados `n=9…192`, os demais nós, quadraturas, a caixa completa, a ponte
CSV–Lean, inclusão dos coeficientes originais da fonte C2 ou sinais finais.
C5 permanece incompleta. Próximo passo: `n=9`.

## Pins e ambiente

- Base da `main`: `e6a05bb60a866502400d163923d5ae749db48d9c` (PR #254).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` durante a compilação: `63361436 kB`.
- SHA-256 da fonte de prova: `d1239cd9c9a04c80b11c2ca4da00e2c37f7b667a08be476571a19e0109db5626`.
- SHA-256 do probe: `acf9f092ee864fe042561a1baaa8a8f547912f9857e5f993c37a9076f3f3ebb4`.

## Reprodução

Compile primeiro os estados integrados até `n=7`, conforme
`../c5-m2-dirichlet-term-stage7-20261107/README.md`, usando o diretório de
saída compartilhado `.cache/c5-m2-term`. Na raiz da worktree:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage8ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage8Certificate
```

`state-stage8-export-probe.log` contém os extremos exportados e
`state-stage8-build.log` contém a compilação e auditoria do certificado.
Checksums: `SHA256SUMS.txt`.

## Publicação

A PR #255 integrou o commit de prova
`96f5f5709829282756bc8c8a2b52a80290c96735` na `main`, pelo merge
`29d363068d52c62c37afc3896f6b3d46f734f16b`. O GitHub não reportou checks
hospedados. Este checkpoint é parcial e não conclui C5.
