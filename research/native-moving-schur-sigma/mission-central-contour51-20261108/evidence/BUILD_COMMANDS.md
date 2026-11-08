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

## C5 zero-displacement transport and ten-mode box sensitivity

The shared generic source recurrence was compiled into the exclusive C2 output root,
because its OLean was not present in the imported B1/B2 artifact paths. `SourceBezout` is its
prerequisite; this did not use the C5 worktree or cache. The first `SigmaSourceBezout` attempt is
preserved as `C5_SourceBezout-missing-dependency.log`; after compiling `SourceBezout`, the module
compiled successfully to `/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaSourceBezout.olean`.

The generic source dependency/provenance audit compiled with the same environment as above:

```bash
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-contour51-20261108-lean432 \
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108 \
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/external:/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432:/home/thlinux/tmp/c2-central-hankel2-20261107-lean432:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaSourceBezoutAudit \
  > /home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaSourceBezoutAudit-attempt1.log 2>&1
```

It reports `57,386` type/body dependencies, standard axioms only, and confirms the original
density/product and sigma moments are retained. The evidence copy is
`C5_source_transport_audit.log`.

`SigmaContour51BoxSensitivity` used the same environment template with
`MODULE_NAME=SigmaContour51BoxSensitivity` and redirected to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51BoxSensitivity-attempt12.log`.
It proves the six rational width budgets, the source-jet lower-margin interface, and the exact
`d=0` C5 source specialization (the displaced product is `completedNativeOperatorCharacteristic²`
and equals `completedNativeCharacteristicContinuation²` under the genuine-strip condition, the source
coefficient is `2H_n`, and the residual-to-source-moment identity). The successful axiom audit reports only `[propext, Classical.choice, Quot.sound]` for
each new theorem, including the strip-conditioned continuation bridge. The final log is
`C2_SigmaContour51BoxSensitivity-attempt12-success.log`; failed attempts 1–7 and 10, and
intermediate attempts 8 and 11, are preserved alongside it. The exact Fraction diagnostic command is
`python3 research/native-moving-schur-sigma/mission-central-contour51-20261108/analyze_box_width_sensitivity.py`,
with output in `evidence/C2_box_sensitivity.log`. Its comparisons with mpmath residual probes are
only refinement diagnostics and do not certify signs.

## Reproduce the PR #306 experiment

```bash
python3 research/native-moving-schur-sigma/mission-central-contour51-20261108/reproduce.py \
  > research/native-moving-schur-sigma/mission-central-contour51-20261108/evidence/PR306-reproduce.log 2>&1
```

## Original-source Arb residual intervals and Lean adapter

The six residual intervals were generated with:

```bash
python3 research/native-moving-schur-sigma/mission-central-contour51-20261108/certify_contour51_residuals.py \
  --arcs 4096 --precision 160 \
  --json research/native-moving-schur-sigma/mission-central-contour51-20261108/evidence/C3_ARb_RESIDUALS_4096.json \
  > research/native-moving-schur-sigma/mission-central-contour51-20261108/evidence/C3_ARb_RESIDUALS_4096.log 2>&1
```

Environment: Python 3.12, `python-flint` 0.8.0, Arb precision 160 bits, Taylor degree 32. The
script reuses `certify_contour51_bound.certify_arc`; it evaluates complete interval arcs and applies
exact rational arc widths. The output JSON stores outward rational endpoints. This is an external
Arb certificate, not itself a Lean theorem.

`SigmaContour51ArbResidualGate` compiled with the common Lean environment above and
`MODULE_NAME=SigmaContour51ArbResidualGate`, redirecting output to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArbResidualGate-attempt7.log`.
The success copy is `C2_SigmaContour51ArbResidualGate-attempt7-success.log`. Attempts 1–6 are
preserved as diagnostics. The module verifies exact rational endpoint simplifications and proves
conditional source-residual, first-window, and all-window theorems. Its interval-transfer
proposition remains open; no external certificate is treated as an axiom or theorem.
