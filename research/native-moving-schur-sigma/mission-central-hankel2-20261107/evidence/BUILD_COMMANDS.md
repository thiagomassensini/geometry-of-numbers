# Reproducible B1 validation commands

Run each Lean command only after confirming there is no active C5 Lean process. The command output
and any Lean diagnostics belong in the mission-owned log directory under
`/home/thlinux/tmp/c2-central-hankel2-20261107-lean432/logs/`.

## Pure algebra and rational gate

```bash
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-central-hankel2-20261107-lean432 \
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-central-hankel2-allorder-20261107 \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaCentralTenModeAlgebra \
  > /home/thlinux/tmp/c2-central-hankel2-20261107-lean432/logs/SigmaCentralTenModeAlgebra.log 2>&1
```

Repeat with `SigmaCentralTenModeRationalGate` after Algebra succeeds.

## Original-source gate and axiom audit

These two imports use only the read-only, hash-matched C2 integration cache. The output remains in
the mission-owned directory.

```bash
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-central-hankel2-20261107-lean432 \
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-central-hankel2-allorder-20261107 \
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaCentralTenModeSourceGate \
  > /home/thlinux/tmp/c2-central-hankel2-20261107-lean432/logs/SigmaCentralTenModeSourceGate.log 2>&1
```

Repeat with `SigmaCentralTenModeAxiomAudit` after SourceGate succeeds, then run:

```bash
python3 research/native-moving-schur-sigma/mission-central-hankel2-20261107/check_sigma_central_axioms.py \
  /home/thlinux/tmp/c2-central-hankel2-20261107-lean432/logs/SigmaCentralTenModeAxiomAudit.log
```
