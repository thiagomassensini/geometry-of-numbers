# Restart point — central C2 Hankel 2×2 positivity

Updated: 2026-11-08 (America/Sao_Paulo)

## State

- Objective: prove the original-source theorem `∀ s, 0 < CarrySigmaPade.sigmaPadeD 0 s`; minimum deliverable is the explicit conditional B1 theorem.
- Base: `origin/main` = `ebd6c57c33edcf8596f09889c7bf956e7d9b284f` (fast-forwarded after C5 PR #303; local branch is aligned before the B1 commit).
- Worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-central-hankel2-allorder-20261107`.
- Branch: `agent/c2-central-hankel2-allorder-20261107`, currently at the same SHA as `origin/main`; no remote branch/PR yet.
- Lean pin: `leanprover/lean4:v4.32.0`.
- Check Geometry open PRs before opening the B1 PR. Momentos PR #2 remains open at `49c9e53946708e3ac1690c25fe096a723ab7bf7d`.
- The C5 initial build and clean reproduction loops have exited. At the 2026-11-08 05:15 UTC process check no Lean, Lake, or C5 reproduction process was active. B1 never used or modified a C5 cache or worktree.
- The new output root for this mission is `/home/thlinux/tmp/c2-central-hankel2-20261107-lean432`; set `SIGMA_OUTPUT_DIR` to its absolute path and `SIGMA_REFERENCE_ROOT` to this worktree. No output/cache from C5 is reused.
- For `SigmaCentralTenModeSourceGate` and its audit, set `SIGMA_HEIGHT50_BUILD=/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/integration:/home/thlinux/geometry-of-numbers/.lake/build/lib/lean`. Both paths are read-only. The second supplies the tracked `CanonicalFiniteHeight` import from Geometry of Numbers commit `d1577400c0d61bc90ecfd1f5759b8e4aaf5fc241`.

## Last verified work

- Read the objective and the full companion audit.
- Fetched `origin` and created this isolated worktree from `origin/main`.
- Read the live declarations for `sigmaPadeD`, `sigmaZeroCount50`, `sigmaRHHeight50`, `sigmaTenZeroBoxesWithFirst`, the height-50 location/order bridge, native continuation, and the original jet definition/normalization.
- Read the all-window and Lehman-contour notes at Momentos PR #2 head. All-window note SHA256: `f34cd0fff357eb57c9ab371c67d1cf18781e2b209d769fcf7bd88cfc2eb2f478`; exact `Fraction` checker SHA256: `cd6e521411eb2ff1cdb4db55e61bbcc6c4ef22a6d293615e47ff488faecd775c`; contour note SHA256: `903e8ae20f6fbea1563fe7a0d6807d6687b74b70ffc092d423500650bd0f8b71`.
- `SigmaCentralTenModeAlgebra`, `SigmaCentralTenModeRationalGate`, `SigmaCentralTenModeSourceGate`, and `SigmaCentralTenModeAxiomAudit` all compile with warnings as errors. The fail-closed audit passes for eight theorem closures using only `propext`, `Classical.choice`, and `Quot.sound`. Logs and source/output hashes are in `evidence/lean-432/BUILD_RESULTS.md`.
- Replayed the exact `Fraction` checker from Momentos PR #2 and separately checked that the coarse global tail bound alone gives a negative D0 lower bound, while refined T1 gives a positive lower bound.
- The theorem keeps the original `completedSigmaLogJet` and `sigmaPadeD` as the source. It assumes the ten-mode decomposition, scale boxes, global error bound, low-index signs, and refined tails explicitly. The analytic bridge deriving those assumptions remains open.

## First action on resume

Recheck `git status --short --branch`, `git log -15 --oneline`, fetch `origin`, and check whether the B1 PR already exists. Update the B1 docs, commit the compiled conditional checkpoint, push the branch, and open a small PR. Do not claim the unconditional theorem while the analytic bridge remains open.

## Last compiled theorem

`CarrySigmaPade.sigmaPadeD_center_pos_of_conditional_ten_mode_tail`, compiled in `SigmaCentralTenModeSourceGate.lean`. This is conditional; the unconditional all-window theorem is not proved.
