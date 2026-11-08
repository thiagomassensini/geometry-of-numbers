# B2 Lean 4.32 build commands

Output root: `/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432`.
Before every compile, verify that no Lean/Lake process from C5 is active.

```bash
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432 \
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-central-ten-heights-b2-20261108 \
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh MODULE_NAME \
  > /home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432/logs/MODULE_NAME.log 2>&1
```

Replace `MODULE_NAME` with the one B2 module being compiled. Keep both cache paths read-only; do not include any C5 cache.
