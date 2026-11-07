# C5 — termo nodal `m=2`, transição Taylor `n=14→15` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage15Certificate.lean` prova
`c5RoundedExpStateC_stage15_correct`, estendendo o estado certificado em
`n=14`. A transição verifica o produto intervalar, o termo com coeficiente
`1/14! = 1/87178291200`, os arredondamentos em 896 bits e a soma acumulada.

Lean 4.32.0 com `warningAsError=true` compilou com `BUILD_EXIT=0`. As cinco
raízes auditadas dependem somente de `propext`, `Classical.choice` e
`Quot.sound`, sem `sorryAx`. O SHA-256 do `.olean` gerado localmente é
`1d9ad02c7ebb14ebde4a0535555aab5e6e9869cad956dc1822cc7e97b372b574`.
Fontes, probe, logs e hashes estão preservados neste diretório.

O probe exportou seis extremos racionais. A potência resultante é negativa,
o termo de Taylor é positivo e a soma acumulada continua positiva.

O escopo cobre somente a recorrência de Taylor até `n=15` em um nó. Não cobre
`n=16…192`, os demais nós, quadraturas, a caixa completa, a ponte CSV–Lean,
a inclusão dos coeficientes da fonte C2 ou os sinais C5 finais. C5 permanece
incompleta.

## Pins e ambiente

- Base da `main`: `7918b5d819ecb938af918f9ab67282010fb8197b` (PR #268).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` após a compilação: `63403340 kB`.
- SHA-256 da fonte de prova: `5bae27ec8506eb9e5073ee6225847e6a7df21501c46a02599926cf3ff3ddb3b8`.
- SHA-256 do probe: `0eb213fb72ff34ef5d176c0704f957bcf024bf52ce2447286268ae65a0349a03`.

## Reprodução

Na raiz da worktree, compile o probe e depois o certificado com o output
compartilhado que contém as etapas anteriores:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage15ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage15Certificate
```

`state-stage15-export-probe.log` contém os limites racionais e o status da
execução bem-sucedida; `state-stage15-build.log` registra a auditoria de
axiomas.

## Publicação

A PR #269 integrou o commit de prova `2dd2bb75153245bb13613135a66721f7a992fcea` na `main` pelo merge
`fe6d5c238ba9ee796dc5ef56880aa60e89899c63`. O GitHub não reportou checks hospedados. Esta validação é parcial e
não conclui C5.
