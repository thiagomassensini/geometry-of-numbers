# Build commands — radius-51 contour route

## C3 generic complex interval division

The division soundness layer compiled with Lean 4.32.0 and warnings as errors in the exclusive C2
output root. It imports the existing rational rectangle and complex interval APIs; no C5 build
output is used.

```bash
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-contour51-20261108-lean432 \
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108 \
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/external:/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432:/home/thlinux/tmp/c2-central-hankel2-20261107-lean432:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaContour51ComplexIntervalDivision
```

Successful output is `C3_SigmaContour51ComplexIntervalDivision-success.log`. The four `#print
axioms` lines contain only standard axioms. The theorem requires a caller-supplied positive
norm-square enclosure and does not verify the evaluator components or per-arc inclusions.

## C3 response and residual interval composition

This module proves the arithmetic composition from explicit component boxes to the original
response and residual quotient. The component boxes, their positive norm-square lower bounds, and
the comparisons with the Arb endpoints remain hypotheses.

```bash
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-contour51-20261108-lean432 \
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108 \
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/external:/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432:/home/thlinux/tmp/c2-central-hankel2-20261107-lean432:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaContour51ArbIntervalComposition
```

The successful output is `C3_SigmaContour51ArbIntervalComposition-success.log`; the memo records
the compile audit and hashes. The endpoint adapter proves only n=0. The generic quotient lemma is
for every n, but closing the first determinant still needs the n=1 and n=2 component-box and
endpoint comparisons.

## Reuse of the zeta Taylor coefficient table for its derivative

`SigmaContour51TaylorCoefficientBridge` proves the exact coefficient shift
`c_k(deriv f)=(k+1)c_(k+1)(f)` and derives a derivative-polynomial interval box from the same
rational coefficient boxes used for `f`. `contourTaylorCauchyValueAndDerivativeBoxes` combines
the generic value and derivative Cauchy bounds into simultaneous boxes. It does not certify any
zeta coefficient or Cauchy input.
The Lean 4.32.0 build used the exclusive output root and common environment above:

```bash
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-contour51-20261108-lean432 \
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108 \
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/external:/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432:/home/thlinux/tmp/c2-central-hankel2-20261107-lean432:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaContour51TaylorCoefficientBridge
```

Attempts 1 and 3 failed during proof-script development and are retained as
`C3_SigmaContour51TaylorCoefficientBridge-attempt1-failed.log` and
`C3_SigmaContour51TaylorCoefficientBridge-attempt3-failed.log`; attempt 2 was an intermediate
success before the combined Cauchy theorem. Attempt 4 compiled with warnings as errors and is
`C3_SigmaContour51TaylorCoefficientBridge-success.log`. The four theorem audits report only
standard Lean axioms. The source has no `sorry`, `admit`, or declared axiom.

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
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArbResidualGate-attempt10.log`.
The success copy is `C2_SigmaContour51ArbResidualGate-attempt10-success.log`; attempt 8 is an
intermediate successful build with the three-residual interface before exposing the strict
`1/1000000000` determinant lower bound in the theorem conclusion. Attempts 1–7 are preserved as
diagnostics/intermediate results. The module verifies exact rational endpoint simplifications and
proves conditional source-residual, first-window, and all-window theorems. Its interval-transfer
propositions remain open; no external certificate is treated as an axiom or theorem.

## Arb lower-path identity and interval interface

`SigmaContour51ArbContourBridge` compiled with Lean 4.32.0 and warnings treated as errors using the
common environment above and `MODULE_NAME=SigmaContour51ArbContourBridge`, redirecting output to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArbContourBridge-attempt19.log`.
It proves oddness of the original response, π-periodicity of the quotient, continuity from C1's
zero-free boundary, and the exact identity between the normalized full-circle residual and the
lower-path integral evaluated by Arb. It also adapts lower-path interval hypotheses to the previous
residual interval gates and composes the first three with the `s=0` determinant gate. The external
per-arc inclusions remain open; this build proves their exact path-coordinate interface and
conditional consequences, not the Arb enclosures themselves.

## Source response to the completed-xi logarithmic derivative

After adding `contour51OriginalResponse_eq_sigmaXiLogDerivative`, the module was rebuilt with the
same command template and exclusive Lean 4.32.0 output root, using
`MODULE_NAME=SigmaContour51ArbContourBridge` and log
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArbContourBridge-attempt25.log`.
It exited 0 with `-DwarningAsError=true`; all eight audited theorems print only
`[propext, Classical.choice, Quot.sound]`. The C5 build remained isolated in its own worktree and
cache, with about 45 GiB available. The checked-in success copy is
`C3_SigmaContour51ArbContourBridge-build.log`. This theorem links the original source response to
the derivative of Lean's entire completed-xi parameter function.

## Explicit original-source evaluator build

After adding the factor split, Gamma/digamma identity, and direct original-response evaluator
formula, the same Lean 4.32.0 command and exclusive output root were used with
`MODULE_NAME=SigmaContour51ArbContourBridge`, writing to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArbContourBridge-attempt39.log`.
The command exited 0 with `-DwarningAsError=true`. Its checked-in output is
`C3_SigmaContour51ArbContourBridge-attempt39-success.log`; each new theorem's axiom report contains
only `[propext, Classical.choice, Quot.sound]`. Source/OLean/log SHA-256 values are recorded in
`VALIDATION.md`. This proves the pointwise formula from the original source under explicit domain
and nonvanishing conditions. It does not import the external Arb enclosures, validate the per-arc
Taylor/Cauchy bounds in Lean, or integrate their sum.

## Lower-path evaluator-domain build

After proving the geometric side conditions for every lower-path parameter, the module was
rebuilt with `MODULE_NAME=SigmaContour51ArbContourBridge` and the same Lean 4.32.0 command,
exclusive output, and shared-library roots. The successful log was
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArbContourBridge-attempt42.log`;
the checked-in copy is `C3_SigmaContour51ArbContourBridge-attempt42-success.log`. It exits 0 with
warnings treated as errors, and `contour51OriginalResponse_eq_arb_formula_lower_path` reports only
standard axioms. This closes the pointwise source-to-evaluator bridge throughout the lower path;
complete-arc interval transfer and rational weighted-sum comparison remain open.

## Uniform-partition integration adapter — attempt 44

After adding `contour51_intervalIntegral_bounds_of_uniform_partition`, the same Lean 4.32.0
command template and exclusive output root were used with
`MODULE_NAME=SigmaContour51ArbContourBridge`, redirecting output to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArbContourBridge-attempt44.log`.
The checked-in successful output is `C3_SigmaContour51ArbContourBridge-attempt44-success.log`.
It exits 0 with warnings treated as errors; the new theorem's axiom report is
`[propext, Classical.choice, Quot.sound]`.

This generic theorem converts pointwise lower and upper bounds on every closed rational arc
`[k/N,(k+1)/N]` into the integral bounds given by the exact width-weighted endpoint sums. It does
not establish that an Arb range contains the Lean evaluator, validate the Taylor/Cauchy remainders,
or prove the resulting rational sum comparisons. Those remain the inputs needed to apply it to the
4096-arc residual certificate. No C5 cache was used as an output.

## All-six 4096-arc arithmetic and conditional integration

The full six-order source was generated by `generate_contour51_arc_sum_lean.py`, then compiled
sequentially on Lean 4.32.0 with `-DwarningAsError=true` into the exclusive output root. Its success
log is `C3_SigmaContour51ArbArcSumCertificate4096-success.log`; it proves the exact lower/upper
list sums and the twelve weighted aggregate-endpoint comparisons. The compile read the existing
B1/B2, C2 integration/external, Carry, and Mathlib OLean outputs; it did not rebuild those modules
or write into the parallel C5 worktree/cache.

`SigmaContour51ArbContourBridge.lean` was then compiled sequentially with the same Lean 4.32.0
toolchain, `-DwarningAsError=true`, exclusive output root, and read-only dependencies. The successful
log is `C3_SigmaContour51ArbContourBridge-attempt66-success.log`. This build includes the all-six
conditional adapter from per-arc inclusion to the six original lower-path residual intervals. The
Lean environment used the branch source directory and `/home/thlinux/tmp/c2-contour51-20261108-lean432`
first in `LEAN_PATH`, followed by the existing B1/B2, C2 integration/external, Carry, and Mathlib
build directories. No OLean was written to the shared primary checkout or to C5's cache.

## C3 lower-semicircle to full-circle bound

After the geometric reduction theorem and its `#print axioms` audit were added,
`SigmaContour51ArbContourBridge` was recompiled with the common environment above and the exclusive
output root. The successful command redirected to
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArbContourBridge-attempt68.log`;
the evidence copy is `C3_SigmaContour51ArbContourBridge-attempt68-success.log`. It compiled on
Lean 4.32.0 with warnings treated as errors while C5 used its separate authorized worktree/cache;
only the C2 exclusive output root was written.

## C3 generic Cauchy Taylor remainder and interval polynomial transfer

The standalone Taylor module compiled with Lean 4.32.0 and warnings as errors, using the exclusive
C2 output root and read-only B1/B2, C2 integration, Carry, and Mathlib dependencies. C5 continued
in its own worktree/cache; no C5 cache was used as output.

```bash
CARRY_LEAN_ROOT=/home/thlinux/worktrees/carry-sigma-c2-pinned-045369 \
SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-contour51-20261108-lean432 \
SIGMA_REFERENCE_ROOT=/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108 \
SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/external:/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432:/home/thlinux/tmp/c2-central-hankel2-20261107-lean432:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean \
bash research/native-moving-schur-sigma/compile_sigma_pade.sh SigmaContour51TaylorRemainder
```

Successful output is at
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51TaylorRemainder-final.log`
and copied to `C3_SigmaContour51TaylorRemainder-success.log`. It prints all eight theorem axiom
reports. This build verifies generic remainders and interval-box propagation only; Arb coefficient
boxes, disk majorants, arc displacement bounds, and response assembly remain open.

## C3 512-arc response table and conditional `hR`

Generate the exact rational table from the existing Arb CSV:

```bash
python3 research/native-moving-schur-sigma/mission-central-contour51-20261108/generate_contour51_bound_lean.py
```

The exporter uses python-flint 0.8.0 at 160-bit precision and outward-rounds every
`response_upper` ball. `SigmaContour51ArbBoundCertificate512` was compiled with the common Lean
environment and exclusive output root above; the final command output is at
`/home/thlinux/tmp/c2-contour51-20261108-lean432/logs/SigmaContour51ArbBoundCertificate512-attempt6.log`.
Its committed evidence copy verifies the rational table, closed-arc cover, conditional response
to `hR` bridge, and composition with the conditional all-window theorem. Pointwise evaluator
inclusion is still an explicit premise.
