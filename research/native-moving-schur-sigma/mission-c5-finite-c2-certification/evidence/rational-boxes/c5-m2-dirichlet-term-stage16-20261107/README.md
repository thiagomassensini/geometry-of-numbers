# C5 — termo nodal `m=2`, transição Taylor `n=15→16` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage16Certificate.lean` prova
`c5RoundedExpStateC_stage16_correct`, estendendo o estado certificado em
`n=15`. A transição verifica o produto intervalar, o termo com coeficiente
`1/15! = 1/1307674368000`, os arredondamentos em 896 bits e a soma acumulada.

Lean 4.32.0 com `warningAsError=true` compilou com `BUILD_EXIT=0`. As cinco
raízes auditadas dependem somente de `propext`, `Classical.choice` e
`Quot.sound`, sem `sorryAx`. O SHA-256 do `.olean` gerado localmente é
`58337ee5688ff3a4fd2a46ec0b25d3911dfe30222252effbe43515dc4feebe99`.
Fontes, probe, logs e hashes estão preservados neste diretório.

O probe exportou seis extremos racionais. A potência resultante é positiva,
o termo de Taylor é negativo e a soma acumulada continua positiva.

O escopo cobre somente a recorrência de Taylor até `n=16` em um nó. Não cobre
`n=17…192`, os demais nós, quadraturas, a caixa completa, a ponte CSV–Lean,
a inclusão dos coeficientes da fonte C2 ou os sinais C5 finais. C5 permanece
incompleta.

## Pins e ambiente

- Base da `main`: `ff69e4d820566109b2491c300dfcfbb553e8bb9f` (PR #270).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` após a compilação: `63351676 kB`.
- SHA-256 da fonte de prova: `265bab0bbe47ca1146ab56cdb81622214d0a68b6dc7c3f67b48cd19105b9db9f`.
- SHA-256 do probe: `d9718f24a007b43ca42661cad742b4b5b6e32514dc13e4358591b18559f7a1cd`.

## Reprodução

Na raiz da worktree, compile o probe e depois o certificado com o output
compartilhado que contém as etapas anteriores:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage16ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage16Certificate
```

`state-stage16-export-probe.log` contém os limites racionais e o status da
execução bem-sucedida; `state-stage16-build.log` registra a auditoria de
axiomas.

## Publicação

A PR #271 integrou o commit de prova `3e9f0e225e426e92a86430ec6d1a22b093ed04af` na `main` pelo merge
`795caa0eebfaa61874c1fff22c683fb85bdf941a`. O GitHub não reportou checks hospedados. Esta validação é parcial e
não conclui C5.
