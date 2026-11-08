# Build commands — radius-51 contour route

## Isolation

- Before every Lean compile, check Lean/Lake processes and available memory. The user authorized parallel execution on 2026-11-08 while C5 PID `151152` runs in a separate worktree; keep this branch's builds sequential and use only its exclusive output root.
- Use only the exclusive output `/home/thlinux/tmp/c2-contour51-20261108-lean432`.
- Use the existing C2 integration/external, B2, B1, and Mathlib outputs read-only; do not rebuild C2/C3 or write into C5 caches.

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

## Reproduce the PR #306 experiment

```bash
python3 research/native-moving-schur-sigma/mission-central-contour51-20261108/reproduce.py \
  > research/native-moving-schur-sigma/mission-central-contour51-20261108/evidence/PR306-reproduce.log 2>&1
```
