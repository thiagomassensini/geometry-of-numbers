# Restart point — B2 ten-height witnesses and central scales

## Current state

- Issue: [#305](https://github.com/thiagomassensini/geometry-of-numbers/issues/305), read in full.
- B1 dependency: PR [#304](https://github.com/thiagomassensini/geometry-of-numbers/pull/304), open at `6397f479f8c373b59cdffea512bbd8dd95b24fb3`; do not modify its branch or re-prove B1.
- B2 branch: `agent/c2-central-ten-heights-b2-20261108`.
- B2 worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-central-ten-heights-b2-20261108`.
- Base: B1 PR head `6397f479f8c373b59cdffea512bbd8dd95b24fb3`.
- Lean: `leanprover/lean4:v4.32.0`; exclusive output root `/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432`.
- B2.0–B2.3 are complete. B2.1 exports the actual ten heights; B2.2 ties the reciprocal-square scales to those same witnesses and closes B1's `hbox`; B2.3 transports the ten roots and order-one results to the original completed characteristic, with a distinct-count classification of the full height window.
- Source, OLean, successful build logs and failed-attempt logs for B2.1–B2.3 are committed under `evidence/`; hashes and axiom reports are in `VALIDATION.md`.
- C5's active build exited before B2.1 compilation. Every B2 Lean build checked that no Lean/Lake process was active first.

## Next action

Open the B2 PR from `agent/c2-central-ten-heights-b2-20261108` against B1 branch `agent/c2-central-hankel2-allorder-20261107`, then record its URL here. PR #304 remains open and untouched; B1's four other assumptions and unconditional positivity remain open.

## Honesty boundary

Use the original `completedNativeCharacteristicContinuation` and its zeta bridge. The ten-zero data may supply the B1 box premise and root statements; it must not redefine the source sequence. B1's `hdecomp`, `he`, `hnonneg`, and `htail` remain explicit, and unconditional positivity remains pending.
