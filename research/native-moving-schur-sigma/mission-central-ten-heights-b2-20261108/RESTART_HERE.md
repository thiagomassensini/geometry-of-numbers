# Restart point — B2 ten-height witnesses and central scales

## Current state

- Issue: [#305](https://github.com/thiagomassensini/geometry-of-numbers/issues/305), read in full.
- B1 dependency: PR [#304](https://github.com/thiagomassensini/geometry-of-numbers/pull/304), open at `6397f479f8c373b59cdffea512bbd8dd95b24fb3`; do not modify its branch or re-prove B1.
- B2 branch: `agent/c2-central-ten-heights-b2-20261108`.
- B2 worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-central-ten-heights-b2-20261108`.
- Base: B1 PR head `6397f479f8c373b59cdffea512bbd8dd95b24fb3`.
- Lean: `leanprover/lean4:v4.32.0`; exclusive output root `/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432`.
- B2.0–B2.2 are complete. B2.1 exports the actual ten heights; B2.2 ties the reciprocal-square scales to those same witnesses and closes B1's `hbox`.
- Source, OLean, successful build logs and failed first-attempt logs for B2.1/B2.2 are committed under `evidence/`; hashes and axiom reports are in `VALIDATION.md`.
- C5 prefix128 completed before B2.1 compilation. Recheck that no Lean/Lake process is active before every later build.

## Next action

Implement B2.3 using `SigmaRHHeightBridge`: expose the ten original completed-characteristic roots and their order-one results from the B2.1 witness, use evenness for negative ordinates, and prove exhaustiveness on `0 < |Re w| ≤ 50` from the distinct-point count and separate simplicity. Keep the `operatorHeightParameter` and original continuation genealogy explicit. Compile only after confirming no Lean/Lake process is active; audit and commit/push B2.3.

## Honesty boundary

Use the original `completedNativeCharacteristicContinuation` and its zeta bridge. The ten-zero data may supply the B1 box premise and root statements; it must not redefine the source sequence. B1's `hdecomp`, `he`, `hnonneg`, and `htail` remain explicit, and unconditional positivity remains pending.
