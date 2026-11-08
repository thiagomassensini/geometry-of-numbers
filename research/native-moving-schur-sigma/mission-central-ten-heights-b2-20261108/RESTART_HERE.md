# Restart point — B2 ten-height witnesses and central scales

## Current state

- Issue: [#305](https://github.com/thiagomassensini/geometry-of-numbers/issues/305), read in full.
- B1 dependency: PR [#304](https://github.com/thiagomassensini/geometry-of-numbers/pull/304), open at `6397f479f8c373b59cdffea512bbd8dd95b24fb3`; do not modify its branch or re-prove B1.
- B2 branch: `agent/c2-central-ten-heights-b2-20261108`.
- B2 worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-central-ten-heights-b2-20261108`.
- Base: B1 PR head `6397f479f8c373b59cdffea512bbd8dd95b24fb3`.
- Lean: `leanprover/lean4:v4.32.0`; exclusive output root `/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432`.
- B2.0 is complete; no B2 source theorem has yet been added or compiled.
- At 2026-11-08 06:15 UTC, no Lean/Lake/C5 process was active. Recheck before starting a build.

## Next action

Inspect `SigmaHeight50Integration.lean` and add a public theorem that packages `height50_rh_certificate`, `height50_count_certificate`, the first-zero witness, `height50_nine_box_certificates`, and `sigmaTenZeroBoxesWithFirst_of_first_and_nine`. Compile only after confirming the C5 build remains inactive. This is B2.1; commit and push when compiled and audited.

## Honesty boundary

Use the original `completedNativeCharacteristicContinuation` and its zeta bridge. The ten-zero data may supply the B1 box premise and root statements; it must not redefine the source sequence. B1's `hdecomp`, `he`, `hnonneg`, and `htail` remain explicit, and unconditional positivity remains pending.
