# C5 — termo nodal `m=2`, transição Taylor `n=13→14` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage14Certificate.lean` prova
`c5RoundedExpStateC_stage14_correct`, estendendo o estado certificado em
`n=13`. A transição verifica o produto intervalar, o termo com coeficiente
`1/13! = 1/6227020800`, os arredondamentos em 896 bits e a soma acumulada.

Lean 4.32.0 com `warningAsError=true` compilou com `BUILD_EXIT=0`. As cinco
raízes auditadas dependem somente de `propext`, `Classical.choice` e
`Quot.sound`, sem `sorryAx`. O SHA-256 do `.olean` gerado localmente é
`7b578ef91da9b97a121eacdadde87ec2c7108c0e05bccaa86f69fbd1f2ce74b7`.
Fontes, probe, logs e hashes estão preservados neste diretório.

O probe exportou seis extremos racionais. A potência resultante é positiva,
o termo de Taylor é negativo e a soma acumulada continua positiva.

O escopo cobre somente a recorrência de Taylor até `n=14` em um nó. Não cobre
`n=15…192`, os demais nós, quadraturas, a caixa completa, a ponte CSV–Lean,
a inclusão dos coeficientes da fonte C2 ou os sinais C5 finais. C5 permanece
incompleta.

## Pins e ambiente

- Base da `main`: `9fdcbda23aa1a22b104244a2c5b477c36194ad87` (PR #266).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` após a compilação: `63397388 kB`.
- SHA-256 da fonte de prova: `6acdb662e90a0574244a1e3f83d8a18c7c0cf93fe0da0aad912fe129db224eb0`.
- SHA-256 do probe: `3b1a172fbb3de029dbbfe22737a4fc05d25e83d5bce93610e942b943d7295dd6`.

## Reprodução

Na raiz da worktree, compile o probe e depois o certificado com o output
compartilhado que contém as etapas anteriores:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage14ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage14Certificate
```

`state-stage14-export-probe.log` contém os limites racionais e o status da
execução bem-sucedida; `state-stage14-build.log` registra a auditoria de
axiomas.

## Publicação

A PR #267 integrou o commit de prova `eaf5a2a71a5d896d4521e2b7cf969421343b3982` na `main` pelo merge
`b1a7c9b14eb1352cc470508fdb2bf9a8baaea56a`. O GitHub não reportou checks hospedados. Esta validação é parcial e
não conclui C5.
