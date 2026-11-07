# C5 — núcleo certificado do nó trivial `m = 1`

**Estado:** checkpoint parcial. As identidades formais do nó `m = 1` foram
compiladas e auditadas; a prova da igualdade entre a caixa Lean e os extremos
exportados da exponencial ainda está incompleta. C5 permanece aberta.

Integrado pela PR #222, commit de prova
`67e6cf9fdf86ac735b6ade80d2f4a64982968363`, merge na `main`
`e55858690e296d00c88692b8f30902987e853137`; o GitHub não reportou checks
hospedados.

## Resultado validado

- `c5CenteredFastLogSumState_zero` e `c5CenteredFastLog1_one_eq_zero` mostram
  que o logaritmo centrado em `1` é a caixa exata `0`.
- `c5CenteredLogQFromLogTwo_one` e
  `c5CenteredDirichletExponentArg_one` propagam essa identidade até o argumento
  exponencial do termo de Dirichlet `m = 1`, sem hipóteses sobre `S` ou `logTwo`.
- `c5CenteredDirichletTermBoxWithLogTwo_one` reduz o termo a
  `c5RoundedExpC ... (ComplexInterval.exact 0 0)`.
- `c5RoundedExpStateC_zero_succ` prova, para todo estágio positivo, a potência
  nula exata e a soma de Taylor unitária exata. `c5RoundedExpSmall_zero`
  conserva explicitamente a inflação racional do resto de Taylor.

Builds Lean 4.32.0, com `warningAsError=true`, passaram para os módulos
alterados. As três auditorias registradas aqui reportam somente
`propext`, `Classical.choice` e `Quot.sound`. Os logs de build e auditoria e as
fontes das auditorias estão nesta pasta; `SHA256SUMS.txt` registra seus hashes.

## Pins e reprodução

O checkpoint parte de `main` em `c67b2f72e0ad2f331c0966fb3ed82e98655e3df8`.
Foram usados a revisão de referência `caa07002306b555fea5624cc11ab2ea5811a4324`,
Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532` e Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. Consulte
[`pins-and-sha256.txt`](pins-and-sha256.txt).

Da raiz do checkout Geometry:

```bash
C5_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
C5_CARRY_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
C5_OUTPUT="$PWD/.cache/c5-exp-zero-integrated-20261107"
C5_EVIDENCE="$PWD/research/native-moving-schur-sigma/mission-c5-finite-c2-certification/evidence/rational-boxes/c5-trivial-node-kernel-20261107"
C5_CACHE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache
C5_REUSE=/home/thlinux/worktrees/geometry-of-numbers-c5-em-high-order-20261106/research/native-moving-schur-sigma/.cache
mkdir -p "$C5_OUTPUT"
export SIGMA_REFERENCE_ROOT="$C5_REFERENCE_ROOT" CARRY_LEAN_ROOT="$C5_CARRY_ROOT"
export SIGMA_OUTPUT_DIR="$C5_OUTPUT"
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
export SIGMA_HEIGHT50_BUILD="$C5_REUSE/c5-node-instantiation-clean-20261107:$C5_REUSE/c5-centered-node-clean-20261107:$C5_CACHE_ROOT/c3-validation/c1:$C5_CACHE_ROOT/c3-validation/c2/integration:$C5_CACHE_ROOT/c4-clean:$C5_CACHE_ROOT/c4-main-clean"
S=research/native-moving-schur-sigma
bash "$S/compile_sigma_pade.sh" SigmaC5RationalNodePreciseLogBounds
bash "$S/compile_sigma_pade.sh" SigmaC5CenteredLogOneAudit
bash "$S/compile_sigma_pade.sh" SigmaC5RoundedComplexExp
bash "$S/compile_sigma_pade.sh" SigmaC5RoundedExpZeroAudit
bash "$S/compile_sigma_pade.sh" SigmaC5RationalNodeCenteredBoxes
bash "$S/compile_sigma_pade.sh" SigmaC5CenteredDirichletM1Audit
```

The preserved logs are the successful runs used for this checkpoint. The audit
source files use `#print axioms` for the listed declarations. Re-running the
commands above writes fresh logs under the selected output directory.

## Primeiro obstáculo ainda aberto

O argumento e a recorrência em zero estão formalizados, mas não foi provado
que a caixa exponencial do estágio 1 coincide exatamente com os extremos
racionais exportados. A última tentativa tentou fechar as igualdades de
`Int.floor` e `Int.ceil` pela forma inadequada de `Int.floor_eq_iff.mpr`; a
compilação terminou com `BUILD_EXIT=1`. Veja
[`stage1-export-equality-last-attempt.log`](stage1-export-equality-last-attempt.log).
O fonte exato dessa tentativa está preservado como
[`SigmaC5ZeroExpStage1Diagnostic5.failed.lean`](SigmaC5ZeroExpStage1Diagnostic5.failed.lean).
Para repetir o último erro, com o ambiente de build descrito acima:

```bash
cp "$C5_EVIDENCE/SigmaC5ZeroExpStage1Diagnostic5.failed.lean" \
  "$S/SigmaC5ZeroExpStage1Diagnostic5.lean"
bash "$S/compile_sigma_pade.sh" SigmaC5ZeroExpStage1Diagnostic5 \
  > "$C5_OUTPUT/stage1-export-equality-last-attempt.log" 2>&1
C5_STATUS=$?
printf 'BUILD_EXIT=%s\n' "$C5_STATUS" \
  >> "$C5_OUTPUT/stage1-export-equality-last-attempt.log"
```

O `sorryAx` impresso após os erros é recuperação do elaborador e não foi
aceito como resultado. Esta tentativa não invalida as identidades já
compiladas e auditadas acima.

Ainda não há ponte CSV–Lean, inclusão dos coeficientes O3, composição completa
da fonte C2, nem sinal finito de C5. O próximo passo é provar as desigualdades
inteiras exatas que determinam os pisos e tetos do estágio 1 e, em seguida,
retomar a ligação formal das caixas exportadas. Não inferir fechamento de C5
a partir deste checkpoint.
