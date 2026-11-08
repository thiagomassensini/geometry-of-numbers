# Restart point — B2 ten-height witnesses and central scales

## Current state

- Issue: [#305](https://github.com/thiagomassensini/geometry-of-numbers/issues/305), read in full.
- B1 dependency: PR [#304](https://github.com/thiagomassensini/geometry-of-numbers/pull/304), open at `6397f479f8c373b59cdffea512bbd8dd95b24fb3`; do not modify its branch or re-prove B1.
- B2 branch: `agent/c2-central-ten-heights-b2-20261108`.
- B2 worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-central-ten-heights-b2-20261108`.
- Base: B1 PR head `6397f479f8c373b59cdffea512bbd8dd95b24fb3`.
- Lean: `leanprover/lean4:v4.32.0`; exclusive output root `/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432`.
- B2.0 and B2.1 are complete. Public theorem `CarrySigmaObstruction.sigmaHeight50_ten_zero_witnesses_and_count` compiles and has the transitive axiom set `[propext, Classical.choice, Quot.sound]`.
- B2.1 source, OLean, successful log and failed first-attempt log hashes are recorded in `VALIDATION.md`. The successful build log is committed under `evidence/`.
- C5 prefix128 completed before B2.1 compilation. Recheck that no Lean/Lake process is active before every later build.

## Next action

Implement B2.2 in a new module: destruct the public B2.1 witness, define `a i = (ts i)⁻²`, and prove positivity, all rational `scaleLower`/`scaleUpper` bounds, `a 0 > a 1 > 0`, and the no-extra-hypothesis witness of B1's `hbox`. Compile only after confirming no C5 Lean/Lake process is active; then audit and commit/push B2.2.

## Honesty boundary

Use the original `completedNativeCharacteristicContinuation` and its zeta bridge. The ten-zero data may supply the B1 box premise and root statements; it must not redefine the source sequence. B1's `hdecomp`, `he`, `hnonneg`, and `htail` remain explicit, and unconditional positivity remains pending.
