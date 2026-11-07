# C5 — termo nodal `m=2`, transição Taylor `n=5→6` (parcial)

## Resultado validado

No nó `(a,j)=(2/5,0)`, `SigmaC5M2TaylorStateStage6Certificate.lean` prova
`c5RoundedExpStateC_stage6_correct`. O passo certifica o produto intervalar,
o coeficiente `1/5! = 1/120`, o arredondamento do termo e a atualização da
soma usando aritmética racional. O resto de Taylor e a definição original de
`c5RoundedExpStateC` permanecem intactos.

A compilação final foi executada contra Geometry no pin
`bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`, Carry no pin
`045369f6dedcb2e75e9aefed1d12c9f73b9a2532` e Lean 4.32.0, com
`warningAsError=true`. Terminou com `BUILD_EXIT=0`. As cinco declarações
impressas por `#print axioms` dependem somente de `propext`,
`Classical.choice` e `Quot.sound`; não aparece `sorryAx`. O SHA-256 do `.olean`
validado é `963405ae7868914c2ba46c223c1b08545eeed846de45c9d5a79046f1444ff2f9`.
O log integral é `state-stage6-build.log`.

Este resultado cobre somente a recorrência até `n=6` de um único nó. Não prova
os outros termos, as quadraturas, a caixa completa `c5CenteredDirichletTermBox`,
a ponte CSV–Lean, a inclusão dos coeficientes originais da fonte C2 ou os
sinais finais C5. C5 continua incompleta. O próximo passo desta trilha local é
certificar `n=7`.

## Pins e ambiente

- Base da `main`: `850582ec76a9819149df2cbad4eba49f3e666e40` (PR #250).
- Geometry de referência: `bf76ce8f5bb753b377a12ba6dbd5c397e4fb3fc3`.
- Carry: `045369f6dedcb2e75e9aefed1d12c9f73b9a2532`.
- Lean: `leanprover/lean4:v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`).
- `MemAvailable` durante a compilação final: `63373028 kB`.
- SHA-256 da fonte: `d0a02792953b4242a6a6552790bdf81eee50bcb5ac00fbec4f0857bade757c22`.

## Reprodução

Compile primeiro as dependências da recorrência até `n=5`, conforme
`../c5-m2-dirichlet-term-stage5-20261107/README.md`, mantendo o output
compartilhado `research/native-moving-schur-sigma/.cache/c5-m2-term`. O estágio
6 importa o módulo de estágio 5 desse diretório. Na raiz da worktree, configure
os mesmos pins e diretórios de suporte:

```bash
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export SIGMA_OUTPUT_DIR="$PWD/research/native-moving-schur-sigma/.cache/c5-m2-term"
export SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-centered-node-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache/c5-node-instantiation-clean-20261107:/home/thlinux/worktrees/geometry-of-numbers-c5-finite-c2-certification/.lake/build/research/native-moving-schur-sigma/c5-zeta-intervals
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5M2TaylorStateStage6Certificate
```

`state-stage6-build.log` preserva a compilação final, a auditoria e
`BUILD_EXIT=0`. `state-stage6-build1.log` e
`state-stage6-first-run-unpinned.log` preservam duas execuções exploratórias
anteriores sem código de saída registrado; nenhuma delas é usada como
validação. `attempt-isolated-output-missing-stage5.log` preserva a falha ao
compilar num output novo sem incluir o módulo de estágio 5 no caminho de
imports; ela é um erro de configuração do ambiente, não uma falha de prova.
Os checksums de todos os artefatos deste diretório estão em `SHA256SUMS.txt`.

## Publicação

Este checkpoint registra validação parcial. A integração por PR e o merge na
`main` serão anotados aqui e nos registros da missão após sua conclusão.
