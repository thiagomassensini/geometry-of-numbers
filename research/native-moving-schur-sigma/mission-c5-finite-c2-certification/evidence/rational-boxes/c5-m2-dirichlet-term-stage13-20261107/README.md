# C5 — termo nodal `m=2`, transição Taylor `n=12→13` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage13Certificate.lean` prova
`c5RoundedExpStateC_stage13_correct`, estendendo o estado certificado em
`n=12`. A transição verifica o produto intervalar, o termo com coeficiente
`1/12! = 1/479001600`, os arredondamentos em 896 bits e a soma acumulada.

Lean 4.32.0 com `warningAsError=true` compilou com `BUILD_EXIT=0`. As cinco
raízes auditadas dependem somente de `propext`, `Classical.choice` e
`Quot.sound`, sem `sorryAx`. O SHA-256 do `.olean` gerado localmente é
`ae4604641706599ff59b3d6246b6ba0a94ac63500004f5b970116a5b653da52d`.
Fontes, probe, logs e hashes estão preservados neste diretório.

O probe exportou seis extremos racionais. A potência resultante é negativa,
o termo de Taylor é positivo e a soma acumulada continua positiva.

O escopo cobre somente a recorrência de Taylor até `n=13` em um nó. Não cobre
`n=14…192`, os demais nós, quadraturas, a caixa completa, a ponte CSV–Lean,
a inclusão dos coeficientes da fonte C2 ou os sinais C5 finais. C5 permanece
incompleta.

## Pins e ambiente

- Base da `main`: `08f238c465179076a2fb15635e23e513245d3d6d` (PR #264).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` após a compilação: `63327236 kB`.
- SHA-256 da fonte de prova: `05708c81eca774760737780643ed0e8533b053968e3edac44f71c07848dca22c`.
- SHA-256 do probe: `2e3e86fbe0febdd360c56302cbf79a14a8fda2885e0166803b8aa0a3d0f26bba`.

## Reprodução

Na raiz da worktree, compile o probe e depois o certificado com o output
compartilhado que contém as etapas anteriores:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage13ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage13Certificate
```

`state-stage13-export-probe.log` contém os limites racionais e o status da
execução bem-sucedida; `state-stage13-build.log` registra a auditoria de
axiomas.

## Publicação

Checkpoint local preparado sobre `main` em `08f238c465179076a2fb15635e23e513245d3d6d`;
a PR ainda não foi criada. Esta validação é parcial e não conclui C5.
