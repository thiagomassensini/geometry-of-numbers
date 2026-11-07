# C5 — termo nodal `m=2`, transição Taylor `n=17→18` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage18Certificate.lean` prova
`c5RoundedExpStateC_stage18_correct`, estendendo o estado certificado em
`n=17`. A transição verifica o produto intervalar, o termo com coeficiente
`1/17! = 1/355687428096000`, os arredondamentos em 896 bits e a soma acumulada.

Lean 4.32.0 com `warningAsError=true` compilou com `BUILD_EXIT=0`. As cinco
raízes auditadas dependem somente de `propext`, `Classical.choice` e
`Quot.sound`, sem `sorryAx`. O SHA-256 do `.olean` gerado localmente é
`ef40d89c693738ea0c0565fcba24f2edcd5e4063b0d927c5a526b9593ac5e25d`.
Fontes, probe, logs e hashes estão preservados neste diretório.

O probe exportou seis extremos racionais. A potência resultante é positiva,
o termo de Taylor é negativo e a soma acumulada continua positiva.

O escopo cobre somente a recorrência de Taylor até `n=18` em um nó. Não cobre
`n=19…192`, os demais nós, quadraturas, a caixa completa, a ponte CSV–Lean,
a inclusão dos coeficientes da fonte C2 ou os sinais C5 finais. C5 permanece
incompleta.

## Pins e ambiente

- Base da `main`: `0807c1052a9e5ac4464139e1593958a495a80103` (PR #274).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` após a compilação: `63350964 kB`.
- SHA-256 da fonte de prova: `a38ce5838bfbe242560c4c746a740aa73a27bab583c902a3ba101d0dcd57cce4`.
- SHA-256 do probe: `6e832a91001a3cbe12a69a1c766e5d968742fe63106d6868e39723b5c5bf4dab`.

## Reprodução

Na raiz da worktree, compile o probe e depois o certificado com o output
compartilhado que contém as etapas anteriores:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage18ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage18Certificate
```

`state-stage18-export-probe.log` contém os limites racionais e o status da
execução bem-sucedida; `state-stage18-build.log` registra a auditoria de
axiomas.

## Publicação

Checkpoint local preparado sobre `main` em `0807c1052a9e5ac4464139e1593958a495a80103`;
a PR ainda não foi criada. Esta validação é parcial e não conclui C5.
