# Validation ledger

## Environment and isolation

- Lean toolchain: `leanprover/lean4:v4.32.0`.
- Worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-central-hankel2-allorder-20261107`.
- Use this worktree as `SIGMA_REFERENCE_ROOT` and the exclusive output directory `SIGMA_OUTPUT_DIR=/home/thlinux/tmp/c2-central-hankel2-20261107-lean432`.
- Do not read from or write to C5 build caches as a dependency. Do not launch Lean while the C5 process recorded in `RESTART_HERE.md` is active.
- The original-source gate uses the read-only C2 integration cache at `/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration` and `/home/thlinux/geometry-of-numbers/.lake/build/lib/lean` through `SIGMA_HEIGHT50_BUILD`. The second path supplies the tracked `GeometryOfNumbers.Analysis.CanonicalFiniteHeight` import required by the existing C2 `.olean`; its source is committed at `d1577400c0d61bc90ecfd1f5759b8e4aaf5fc241`. The source files for `SigmaPadeCorrespondence`, `SigmaSignedPencil`, `SigmaNeighborhood`, and the `SigmaQuadratic → SigmaCurvature → SigmaCenterAll → SigmaCenterZero → SigmaParity` chain were byte-identical between this worktree and the C2 integration cache's worktree. This does not use a C5 cache.

## Current evidence

- Checkpoint 0 source declarations were first inspected on `origin/main` at `eb00da2374a2a0a5f563ab94925a96c2bb7a019a`. The isolated branch now fast-forwards to `9d45f4e03b3e40186c74e72dba5e8077ecc59f8d` after C5 PRs #300 and #301; all imported C2 source files retain their hash match to the read-only integration cache.
- `SigmaCentralTenModeAlgebra`, `SigmaCentralTenModeRationalGate`, `SigmaCentralTenModeSourceGate`, and `SigmaCentralTenModeAxiomAudit` all compiled with Lean 4.32 and `-DwarningAsError=true`. The only original-source import adjustment was adding the read-only Geometry of Numbers library build that supplies `CanonicalFiniteHeight`; that module's source is tracked at commit `d1577400c0d61bc90ecfd1f5759b8e4aaf5fc241`.
- The fail-closed checker passed all eight audited theorem closures. Each reports exactly `{propext, Classical.choice, Quot.sound}`. `evidence/lean-432/` contains the raw compile/audit logs, checker output, and source/`.olean` SHA256 manifests. The output `.olean` files remain in the mission-owned directory `/home/thlinux/tmp/c2-central-hankel2-20261107-lean432`.
- `origin/main` advanced while waiting for the C5 prefix96 loop; this branch fast-forwarded to `ebd6c57c33edcf8596f09889c7bf956e7d9b284f`. The source files imported from the C2 integration worktree were rechecked byte-identical after that update.
- The `SigmaPadeCorrespondence.olean` in the read-only C2 integration cache has SHA256 `b3111d8cb5bbe9840a3bfb870657c1f6fc69f160be37727b33d6d23507a6a62a`.
- `SigmaCentralTenModeAlgebra`, `SigmaCentralTenModeRationalGate`, and `SigmaCentralTenModeSourceGate` now compile with Lean 4.32 and `-DwarningAsError=true`; their `.olean` hashes are recorded in the mission output root and will be copied into the final evidence ledger after the axiom audit.
- Existing height-50 sources match their prior Lean 4.32 source pins through current `origin/main`; the hash-matched `SigmaHeight50Integration` build log reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Open Geometry PR count at inventory: zero. Momentos PR #2 head: `49c9e53946708e3ac1690c25fe096a723ab7bf7d`.

## Exact rational reference replay

The checker `check_all_central_2x2_boxes_lehman_exact.py` was replayed from the audited Momentos PR #2 head (source SHA256 is recorded in `SESSION_STATE.md`). Its exact `Fraction` assertions passed; decimals below are output formatting only:

```text
High zero tail T0 = 0.022723566878980892 < 60/2500 = 0.024
D_0 > 2.83566043188920e-10
D_1 > 2.68831487875457e-15
D_2 > 1.74257015571398e-20
D_3 > 5.08933215861573e-26
s>=4: relative error at s=4 < 0.40844996142660117 <1
```

The reproduced stdout is saved at `evidence/exact_fraction_replay.log` (SHA256
`2ffe506328086f023dc55d12d7c74630edce5a2b705a2da2944ebeefe2d8e928`). The script SHA256 is
`cd6e521411eb2ff1cdb4db55e61bbcc6c4ef22a6d293615e47ff488faecd775c`.

An additional exact `Fraction` check was run for the critical D0 distinction:

```text
D0 lower bound using only global tail bound = -1.5998689660476498e-10
D0 lower bound using refined T1 = 2.835660431889203e-10
```

This confirms the global tail premise alone cannot establish the shallow window bound used here. The Lean rational gate independently proves the four strict margins and the `s≥4` ratio from exact rational definitions; it does not import the Python checker output.

## B1 validation completed

- All four modules compile with warnings as errors in the Lean 4.32 toolchain.
- `#print axioms` covers the source theorem and seven key public lemmas. All closures use only the allowed standard axioms.
- The fail-closed checker rejects unrecognized axioms and any `sorryAx`, `sorry`, or `admit`; it passes the captured audit log.
- Exact box, margin, ratio, and Fraction replay evidence is recorded under `evidence/`.
- Exact compile commands, source hashes, `.olean` hashes, and raw logs are recorded in `evidence/lean-432/` and `evidence/BUILD_COMMANDS.md`.
- The conditional theorem still depends on analytic assumptions listed in `OPEN_OBLIGATIONS.md`.

## Final validation when the unconditional composition exists

- Compile the complete original-source theorem `∀ s, 0 < CarrySigmaPade.sigmaPadeD 0 s`.
- Audit the full transitive axiom closure and native source/jet/factor-of-two normalization.
- Verify remote PR head, CI/build evidence, merge state, and final remote main SHA before claiming completion.
- Scope statement: central consecutive 2×2 minors only; no higher Hankel PSD or global zero-location conclusion.
