# Build commands — radius-51 contour route

## Isolation

- Before every Lean compile, check Lean/Lake processes and available memory. The user authorized parallel execution on 2026-11-08 while C5 PID `151152` runs in a separate worktree; keep this branch's builds sequential and use only its exclusive output root.
- Use only the exclusive output `/home/thlinux/tmp/c2-contour51-20261108-lean432`.
- Use the existing upstream C2 integration/external, B2, B1, and Mathlib outputs read-only; do not rebuild those upstream C2 modules or the C3 module, and do not write into C5 caches. Contour modules in this branch may be compiled sequentially.

## Lean module compile template

Replace `MODULE_NAME` with one module in the isolated C2 contour branch. This invokes the repository script, which passes `-DwarningAsError=true` and checks the pinned Carry checkout.

```bash
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-contour51-20261108-lean432 \
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108 \
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/external:/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432:/home/thlinux/tmp/c2-central-hankel2-20261107-lean432:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh MODULE_NAME \
  > /home/thlinux/tmp/c2-contour51-20261108-lean432/logs/MODULE_NAME.log 2>&1
```

## C2 residue-helper build

The successful `SigmaContour51Residue` build used the same environment values above, with
`MODULE_NAME=SigmaContour51Residue`, and redirected output to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51Residue-attempt4.log`.
The evidence copy is `C2_SigmaContour51Residue-build.log`. The C5 process remained isolated in
its own worktree/cache; at this build, `/proc/meminfo` reported about 56.6 GiB available.

After updating the helper's documentation to point at the completed global theorem, the module was
recompiled with the same command template as `MODULE_NAME=SigmaContour51Residue`, redirecting to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51Residue-attempt5.log`. The
final evidence copy is `C2_SigmaContour51Residue-attempt5-success.log`.

## C4/C6 conditional-gate build

The successful `SigmaContour51RationalGate` build used the same environment values above, with
`MODULE_NAME=SigmaContour51RationalGate`, and redirected output to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51RationalGate-attempt3.log`.
The evidence copy is `C4C6_SigmaContour51RationalGate-build.log`; failed diagnostic attempts 1
and 2 are preserved beside it. This build ran while C5 PID `151152` was active in its isolated
worktree/cache, under the user's explicit parallel-build authorization; about 56.6 GiB was
available. Builds within this branch remained sequential.

## C2 finite-kernel build

The successful `SigmaContour51FiniteContour` build used the same environment values above, with
`MODULE_NAME=SigmaContour51FiniteContour`, and redirected output to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51FiniteContour-attempt12.log`.
The evidence copy is `C2_SigmaContour51FiniteContour-build.log`; failed diagnostic attempts 1–8
and 11 are preserved beside it, with Lean's trailing whitespace removed from the diagnostic copies.
This build ran while C5 PID `151152` was active in its separate worktree/cache, under the user's
explicit parallel-build authorization; about 56 GiB was available.

## C2 global source-normalized contour identity

The final `SigmaContour51FiniteContour` build, after rebuilding its helper dependency, used the same environment values above and
redirected output to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51FiniteContour-attempt34.log`.
It proves one fixed C1 root list with its ten exact height boxes works for every `n`, globally glues
the finite correction, and identifies the contour coefficient with the original central jet minus
the ten paired modes. The evidence copy is
`C2_SigmaContour51FiniteContour-attempt34-success.log`. The build ran while C5 PID `151152` was
active only in its separate worktree/cache; about 51 GiB was available, and no C5 path was used as
an output.

## C2→C4→C6 source-level conditional closure

`SigmaContour51SourceTail` was compiled with the common environment above, using the same exclusive
output root and redirecting to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51SourceTail-attempt10.log`.
The module composes the all-order original-source contour identity with the `C=40` tail and the
central determinant gates. The source decomposition and reciprocal-square scale boxes are proved
inside the module; the all-window theorem needs only the circle norm bound and six residual signs.
The focused first-window theorem needs the circle bound and just `e_0,e_2≥0`, with the absolute
tail controlling its middle moment. The success log is copied to
`C2_SigmaContour51SourceTail-attempt10-success.log`.

## Reproduce the PR #306 experiment

```bash
python3 research/native-moving-schur-sigma/mission-central-contour51-20261108/reproduce.py \
  > research/native-moving-schur-sigma/mission-central-contour51-20261108/evidence/PR306-reproduce.log 2>&1
```
