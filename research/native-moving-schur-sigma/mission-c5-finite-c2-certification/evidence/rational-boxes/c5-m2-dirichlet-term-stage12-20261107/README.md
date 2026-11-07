# C5 — termo nodal `m=2`, transição Taylor `n=11→12` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage12Certificate.lean` prova
`c5RoundedExpStateC_stage12_correct`, estendendo o estado já certificado em
`n=11`. A transição verifica o produto intervalar, o termo com coeficiente
`1/11! = 1/39916800`, os arredondamentos em 896 bits e a soma acumulada.

Lean 4.32.0 com `warningAsError=true` compilou com `BUILD_EXIT=0`. As cinco
raízes auditadas dependem somente de `propext`, `Classical.choice` e
`Quot.sound`, sem `sorryAx`. O SHA-256 do `.olean` gerado localmente é
`e58f15e3d62382cb03e666ac10e68b088a468bc64403e8838782a1362675b612`.
Fontes, probe, logs e hashes estão preservados neste diretório.

A primeira execução do export probe terminou com `BUILD_EXIT=1`, registrando
`unknown module prefix 'SigmaC5RationalNodeLogBounds'`. Esse log foi preservado.
A repetição do mesmo comando no mesmo ambiente compilou com `BUILD_EXIT=0`,
sem alteração de fonte; o segundo log registra os seis extremos racionais
usados no certificado.

O escopo cobre somente a recorrência de Taylor até `n=12` em um nó. Não cobre
`n=13…192`, os demais nós, quadraturas, a caixa completa, a ponte CSV–Lean,
a inclusão dos coeficientes da fonte C2 ou os sinais C5 finais. C5 permanece
incompleta.

## Pins e ambiente

- Base da `main`: `6288bc32726d64d1b3e1106cabecf81c4bf642e8` (PR #262).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` após a compilação: `63363208 kB`.
- SHA-256 da fonte de prova: `15b8bbcbddd9d11f75234b9bd58681e7e49a3cbe377a44a72fbcd73f3346fc44`.
- SHA-256 do probe: `5795b0dcf5b1500b099c323f54571a77f59ce15b9d775a058cdd02ed116e936e`.

## Reprodução

Na raiz da worktree, compile o probe e depois o certificado com o output
compartilhado que contém as etapas anteriores:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage12ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage12Certificate
```

`state-stage12-export-probe.log` contém os limites racionais e o status da
execução bem-sucedida; `state-stage12-build.log` registra a auditoria de
axiomas. `state-stage12-export-probe-initial-cache-miss.log` preserva a falha
inicial de busca do módulo.

## Publicação

A PR #263 integrou o commit de prova `b7c442c318de488cb928fc8e456110b4b27a81f4` na `main` pelo merge
`4b5b6a0aebd54798e6a26b2eda69994589c78668`. O GitHub não reportou checks hospedados. Esta validação é parcial e
não conclui C5.
