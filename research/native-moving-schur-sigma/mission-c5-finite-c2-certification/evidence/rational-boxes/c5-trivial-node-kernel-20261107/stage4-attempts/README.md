# C5 — tentativa inicial de build do estágio 4

A primeira execução do build terminou antes de verificar as declarações do
estágio 4. O caminho de busca continha os caches dos estágios 2 e 3, mas não o
cache de `SigmaC5RoundedComplexExp.olean`; Lean parou no `import` com
`unknown module prefix 'SigmaC5RoundedComplexExp'`. O log e o caminho usado
estão em `first-build-missing-import-path.log`.

Tentativa inicial, a partir da raiz Geometry:

```sh
STAGE4_CACHE="$PWD/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage4-separated-20261107"
STAGE3_CACHE="$PWD/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage3-separated-20261107"
STAGE2_CACHE="$PWD/research/native-moving-schur-sigma/.cache/c5-zero-exp-stage2-20261107"
export SIGMA_OUTPUT_DIR="$STAGE4_CACHE"
export SIGMA_HEIGHT50_BUILD="$STAGE3_CACHE:$STAGE2_CACHE"
export SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-allorder-negative-certified-20261105
export CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
export LEAN_BIN=/home/thlinux/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaC5ZeroExpStage4Certificate
```

O build seguinte incluiu o cache `c5-exp-zero-integrated` e as dependências
C5 compartilhadas. A prova compilou e a auditoria passou; o erro inicial era
somente a configuração incompleta do caminho de imports, não uma falha de
prova.
