# C5 — termo nodal `m=2`, transição Taylor `n=6→7` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage7Certificate.lean` prova
`c5RoundedExpStateC_stage7_correct`. A transição confere o produto de um
intervalo não-negativo pelo argumento não-positivo, o termo de coeficiente
`1/6! = 1/720`, o arredondamento em 896 bits e a soma acumulada em aritmética
racional.

A compilação passou em Lean 4.32.0 com `warningAsError=true` contra Geometry no
pin `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry no pin
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O log registra `BUILD_EXIT=0`.
As cinco declarações auditadas dependem somente de `propext`,
`Classical.choice` e `Quot.sound`; não há `sorryAx`. O SHA-256 do `.olean` é
`674da4ae60dcdaa7d17543ddfc27a50d7186c26af796c076d2978c589e295011`.

`SigmaC5M2TaylorStateStage7ExportProbe.lean` avalia a recorrência até `n=7` e
exporta os seis extremos racionais usados para montar o certificado. Essa
saída é dado de trabalho, não é a prova; a fonte de certificado verifica as
igualdades por aritmética racional. A fonte, os dois logs, pins, hashes e
comandos estão preservados neste diretório.

O alcance é apenas a recorrência Taylor até `n=7` de um nó. Não prova os
estados `n=8…192`, os demais nós, as quadraturas, a caixa completa
`c5CenteredDirichletTermBox`, a ponte CSV–Lean, a inclusão dos coeficientes
originais da fonte C2 nem os sinais finais. C5 continua incompleta. Próxima
etapa: `n=8`.

## Pins e ambiente

- Base da `main`: `c0d2b4799ce81a5428ee84b68a886bd656441779` (PR #252).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` durante a compilação: `63364896 kB`.
- SHA-256 da fonte de prova: `770854eeae13540e8d9eb7d486bd7db9ffe467560b79f7e2508c3e51d7e033ec`.
- SHA-256 do probe: `1fef6a650bebfaea742877e80e16428c4222369cc1c1b521a9e5ef6ad460e0b9`.

## Reprodução

Compile primeiro os estados integrados até `n=6`, seguindo
`../c5-m2-dirichlet-term-stage6-20261107/README.md`, e mantenha o output
compartilhado `.cache/c5-m2-term`. Da raiz da worktree:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage7ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage7Certificate
```

`state-stage7-export-probe.log` contém os extremos exportados; `state-stage7-build.log`
contém a compilação e a auditoria do certificado. Os checksums estão em
`SHA256SUMS.txt`.

## Publicação

A PR #253 integrou o commit de prova
`a08a5c9c5a1d02fc33b3207ef2be3d362d526de8` na `main`, pelo merge
`952fcd76093681f3feacc540bb0db9c49bfc6034`. O GitHub não reportou checks
hospedados. Este continua sendo um checkpoint parcial; C5 não está concluída.
