# C5 — termo nodal `m=2`, transição Taylor `n=16→17` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage17Certificate.lean` prova
`c5RoundedExpStateC_stage17_correct`, estendendo o estado certificado em
`n=16`. A transição verifica o produto intervalar, o termo com coeficiente
`1/16! = 1/20922789888000`, os arredondamentos em 896 bits e a soma acumulada.

Lean 4.32.0 com `warningAsError=true` compilou com `BUILD_EXIT=0`. As cinco
raízes auditadas dependem somente de `propext`, `Classical.choice` e
`Quot.sound`, sem `sorryAx`. O SHA-256 do `.olean` gerado localmente é
`b406ac60313f830cbc88b412ad0a454e5966be8fb8ed1cf7d602fa41190e153f`.
Fontes, probe, logs e hashes estão preservados neste diretório.

O probe exportou seis extremos racionais. A potência resultante é negativa,
o termo de Taylor é positivo e a soma acumulada continua positiva.

O escopo cobre somente a recorrência de Taylor até `n=17` em um nó. Não cobre
`n=18…192`, os demais nós, quadraturas, a caixa completa, a ponte CSV–Lean,
a inclusão dos coeficientes da fonte C2 ou os sinais C5 finais. C5 permanece
incompleta.

## Pins e ambiente

- Base da `main`: `00ea9d49245e701884db695ce718279deab43056` (PR #272).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` após a compilação: `63399680 kB`.
- SHA-256 da fonte de prova: `3b4af90dadf4234fb2f724c78858c36f325d5b0833778859303c9f6994a77dac`.
- SHA-256 do probe: `cd3ab0e00d099f18b1bb0ef9db1f506059085a005e60ff6cdf4e3f76ce64c6b3`.

## Reprodução

Na raiz da worktree, compile o probe e depois o certificado com o output
compartilhado que contém as etapas anteriores:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage17ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage17Certificate
```

`state-stage17-export-probe.log` contém os limites racionais e o status da
execução bem-sucedida; `state-stage17-build.log` registra a auditoria de
axiomas.

## Publicação

A PR #273 integrou o commit de prova `0783b090aa4f9b6faf7ecd3605c187ae46352498` na `main` pelo merge
`41164de6cf0042594833bae02cdab2ce4cd11aae`. O GitHub não reportou checks hospedados. Esta validação é parcial e
não conclui C5.
