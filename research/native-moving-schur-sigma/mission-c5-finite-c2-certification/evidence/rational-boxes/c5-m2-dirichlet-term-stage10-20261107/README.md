# C5 — termo nodal `m=2`, transição Taylor `n=9→10` (parcial)

## Resultado validado localmente

Para `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage10Certificate.lean` prova
`c5RoundedExpStateC_stage10_correct`. O passo certifica o produto de
intervalos não-positivos, o coeficiente `1/9! = 1/362880`, o coarsening em 896
bits, a atualização da soma e os extremos racionais.

A compilação passou em Lean 4.32.0 com `warningAsError=true`, Geometry no pin
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3` e Carry no pin
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532`. O log termina em
`BUILD_EXIT=0`. As cinco declarações auditadas dependem somente de
`propext`, `Classical.choice` e `Quot.sound`; não há `sorryAx`. SHA-256 do
`.olean`: `65e5c8e597243335c88cca90a3144f5342504b62087fd7c0cee76144b77fc4df`.

`SigmaC5M2TaylorStateStage10ExportProbe.lean` exporta os extremos usados para
compor o certificado. Sua saída de `#eval` é dado de construção, não prova;
as igualdades são demonstradas pela fonte de certificado. As fontes e os logs
estão preservados neste diretório.

O escopo é somente a recorrência Taylor até `n=10` de um nó. Não prova
`n=11…192`, os outros nós, quadraturas, a caixa completa, a ponte CSV–Lean, a
inclusão da fonte C2 ou os sinais finais. C5 permanece incompleta. Próximo:
`n=11`.

## Pins e ambiente

- Base da `main`: `72d91196e14289f1818e33b539776f6fa80f8413` (PR #258).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` durante a compilação: `63371140 kB`.
- SHA-256 da fonte de prova: `6f9b391544eeeb5bde17e96b43786deaa9b83e0a0a39c83274591c4cb7993808`.
- SHA-256 do probe: `b8cc83cfe319d41758f2a839527cbf2e7f6b0512fd1d4e32a5c0fadfd08c0c23`.

## Reprodução

Compile primeiro os módulos até `n=9` conforme
`../c5-m2-dirichlet-term-stage9-20261107/README.md`, mantendo o output
compartilhado `.cache/c5-m2-term`. Na raiz da worktree:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage10ExportProbe
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage10Certificate
```

`state-stage10-export-probe.log` registra os extremos exportados;
`state-stage10-build.log` registra build e auditoria. Checksums em
`SHA256SUMS.txt`.

## Publicação

Este checkpoint está local e ainda não foi publicado por PR. C5 permanece
incompleta.
