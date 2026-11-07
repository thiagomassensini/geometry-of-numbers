# C5 — núcleo certificado do nó trivial `m = 1`

**Estado:** checkpoint parcial. As identidades formais do nó `m = 1` e as
igualdades das caixas arredondadas nos estágios 1, 2 e 3 foram compiladas e
auditadas. A ponte CSV–Lean e as inclusões dos coeficientes C2 continuam
abertas; C5 não está concluída.

Integrado pela PR #222, commit de prova
`67e6cf9fdf86ac735b6ade80d2f4a64982968363`, merge na `main`
`e55858690e296d00c88692b8f30902987e853137`; o GitHub não reportou checks
hospedados.

A igualdade do estágio 1 foi integrada pela PR #224, commit de prova
`a908789fad182aa9a2d8eb85b2da641c11c4da62`, merge na `main`
`d667abfc42020e442c62ec1b49b82f5bcf1971ad`; o GitHub não reportou checks.

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

## Igualdades exatas dos estágios 1 e 2

`SigmaC5ZeroExpStagesCertificate.lean` prova que
`c5RoundedExpC 192 896 1 (ComplexInterval.exact 0 0)` é exatamente
`c5ZeroExpStage1Export`. Quatro lemas verificam os pisos e tetos dos extremos
da caixa quadrada por desigualdades racionais exatas. A auditoria isolada
reporta somente `propext`, `Classical.choice` e `Quot.sound` para os quatro
lemas de arredondamento, a identidade de estágio 0 e a identidade de estágio 1.
Essa prova foi integrada pela PR #224, commit de prova
`a908789fad182aa9a2d8eb85b2da641c11c4da62`, merge
`d667abfc42020e442c62ec1b49b82f5bcf1971ad`.

O build de prova passou em Lean 4.32.0 com `warningAsError=true`; a auditoria
por import passou separadamente. Logs, fontes, hash do `.olean`, hash dos
registros e uma tentativa redundante interrompida estão preservados em
`SigmaC5ZeroExpStagesCertificate.stage1-build.log`,
`SigmaC5ZeroExpStagesCertificate.stage1-axioms.log`,
`stage1-pins.txt` e `stage1-sha256.txt`. Uma recompilação redundante com as
linhas `#print axioms` dos quatro lemas auxiliares dentro do módulo foi
interrompida após 3 minutos; outra compilação limpa do mesmo corpo de prova foi
interrompida após 5 minutos de redução racional. Nenhuma relatou erro
matemático. O build anterior desse mesmo corpo terminou com código zero, e o
módulo de auditoria importado compilou com código zero. As duas interrupções
estão em `SigmaC5ZeroExpStagesCertificate.extra-full-build-interrupted.log` e
`SigmaC5ZeroExpStagesCertificate.final-rebuild-interrupted.log`.

`c5ZeroExpStage2_eq` prova que `c5RoundedExpC 192 896 2` na entrada zero é
exatamente `c5ZeroExpStage2Export`. Quatro lemas adicionais verificam os
pisos/tetos da caixa quadrada de estágio 1. O build e a auditoria das onze
declarações passaram em Lean 4.32.0; somente `propext`, `Classical.choice` e
`Quot.sound` aparecem. Logs, pins e hashes estão em
`SigmaC5ZeroExpStagesCertificate.stage2-build.log`,
`SigmaC5ZeroExpStagesCertificate.stage2-axioms.log`, `stage2-pins.txt` e
`stage2-sha256.txt`. A PR #226 integrou esse subpasso, commit de prova
`ab0f2782369e7f0966fa6c769d23ca18ea9abb1f`, merge
`96579150be6700793970bf8cd84f91dd2cccb102`; o GitHub não reportou checks.

`SigmaC5ZeroExpStage3Certificate.lean` importa a prova integrada do estágio 2
e prova `c5ZeroExpStage3_eq`, igualando `c5RoundedExpC 192 896 3` na entrada
zero a `c5ZeroExpStage3Export`. Quatro lemas exibem os extremos racionais da
caixa quadrada e quatro certificam seus pisos/tetos. O build limpo e a auditoria
das nove declarações passaram em Lean 4.32.0, somente com axiomas padrão. Logs,
pins e hashes estão em `SigmaC5ZeroExpStage3Certificate.build.log`,
`SigmaC5ZeroExpStage3Audit.log`, `stage3-pins.txt` e `stage3-sha256.txt`.
Tentativas de expansão direta e a sonda que isolou as fórmulas estão em
`stage3-attempts/`. Este checkpoint está validado localmente; a publicação
aguarda a PR deste checkpoint.

## Pins e reprodução

O checkpoint original do nó `m = 1` parte de `main` em
`c67b2f72e0ad2f331c0966fb3ed82e98655e3df8`; os pins das validações dos estágios
1 e 2 estão em [`stage1-pins.txt`](stage1-pins.txt) e [`stage2-pins.txt`](stage2-pins.txt).
Para o checkpoint original,
foram usados a revisão de referência `caa07002306b555fea5624cc11ab2ea5811a4324`,
Carry `045369f6dedcb2e75e9aefed1d12c9f73b9a2532` e Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`; veja também
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
bash "$S/compile_sigma_pade.sh" SigmaC5ZeroExpStagesCertificate
bash "$S/compile_sigma_pade.sh" SigmaC5ZeroExpStagesAudit
bash "$S/compile_sigma_pade.sh" SigmaC5ZeroExpStage3Certificate
bash "$S/compile_sigma_pade.sh" SigmaC5ZeroExpStage3Audit
```

The preserved logs are the successful runs used for this checkpoint. The audit
source files use `#print axioms` for the listed declarations. Re-running the
commands above writes fresh logs under the selected output directory.

## Próxima obrigação aberta

Os estágios 1, 2 e 3 agora estão provados. A tentativa que falhou ao aplicar diretamente
`Int.floor_eq_iff.mpr` e `Int.ceil_eq_iff.mpr` permanece como histórico; veja
[`stage1-export-equality-last-attempt.log`](stage1-export-equality-last-attempt.log).
O fonte exato dessa tentativa está preservado como
[`SigmaC5ZeroExpStage1Diagnostic5.failed.lean`](SigmaC5ZeroExpStage1Diagnostic5.failed.lean).
Para repetir esse erro histórico, com o ambiente de build descrito acima:

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
da fonte C2, nem sinal finito de C5. O próximo passo é avançar o estágio 4 da
exponencial e depois ligar formalmente as caixas exportadas,
compondo zeta, Gamma, o fator dependente de π e a fonte C2 original. Não
inferir fechamento de C5 a partir deste checkpoint.
