# Lean 4.32 C5 transport build record

The two new C5 Lean modules were compiled with `warningAsError=true` using
`research/native-moving-schur-sigma/compile_sigma_pade.sh` and a fresh output directory:

```text
SIGMA_OUTPUT_DIR=.lake/build/research/native-moving-schur-sigma/c5-lean432-clean
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c1:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c4-main-clean
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369
LEAN_BIN=/home/thlinux/.elan/bin/lean
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaFiniteCoefficientSignTransport
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaFiniteCoefficientSignTransportAudit
```

Both invocations exited with status 0. Lean emits no stdout on successful compilation, so
`build-transport-clean.log` is empty; the produced `.olean` hashes are recorded in
`pins-and-sha256.txt`. The audit module prints all four theorem footprints in
`axiom-audit-transport-clean.log`.
