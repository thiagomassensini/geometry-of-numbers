# C5 — termo nodal `m=2`, transição Taylor `n=10→11` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage11Certificate.lean` prova
`c5RoundedExpStateC_stage11_correct`. O passo verifica o produto intervalar
de sinais conhecidos, o termo com coeficiente `1/10! = 1/3628800`, os
arredondamentos em 896 bits e a soma acumulada.

Lean 4.32.0 com `warningAsError=true` passou contra Geometry no pin
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry no pin
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O log registra `BUILD_EXIT=0`.
As cinco raízes auditadas dependem somente de `propext`, `Classical.choice` e
`Quot.sound`, sem `sorryAx`. SHA-256 do `.olean`:
`93592224ffcca6e21a2d66f9d787648a56bc4ad49fdf6c3b9458baad0e77937e`.

O export probe imprime os extremos racionais usados para montar o certificado.
Seu `#eval` é dado de construção; a prova de igualdade está no módulo de
certificado Lean. Fonte, probe e logs estão preservados aqui.

O escopo é apenas a recorrência Taylor até `n=11` de um nó. Não cobre
`n=12…192`, outros nós, quadraturas, caixa completa, ponte CSV–Lean, inclusão
dos coeficientes da fonte C2 ou sinais finais. C5 continua incompleta.

## Pins e ambiente

- Base da `main`: `29377f9d59f5ad36e2a4447f445de3898649324d` (PR #260).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` durante a compilação: `63344696 kB`.
- SHA-256 da fonte de prova: `09caca39e54f0699133af1901fb664693eca479bc8cbfab88bfca4a019c8fc07`.
- SHA-256 do probe: `8026d5b7f46b3232f4fe58d08c4908737060c48e7a24b9ad3c2bc492625ef3cc`.

## Reprodução

Compile primeiro os módulos integrados até `n=10` conforme
`../c5-m2-dirichlet-term-stage10-20261107/README.md`, mantendo o output
compartilhado `.cache/c5-m2-term`. Na raiz da worktree:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage11ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage11Certificate
```

`state-stage11-export-probe.log` contém os extremos exportados e
`state-stage11-build.log` contém build e auditoria. Os hashes dos artefatos
estão em `SHA256SUMS.txt`.

## Publicação

Este checkpoint está local, sem PR ou merge. Ele é parcial e não conclui C5.
