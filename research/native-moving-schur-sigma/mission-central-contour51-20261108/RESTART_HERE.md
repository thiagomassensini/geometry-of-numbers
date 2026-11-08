# Restart point — radius-51 contour route

## Current state

- Read the full PR #306 investigation, copied it into this branch, and reproduced its Python probe. The grid and floating-point jet values remain experimental evidence only.
- Worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108`.
- Branch: `agent/c2-contour51-20261108`.
- Base: B2 PR #311 head `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`; B1 is inherited through B2.
- Exclusive Lean output: `/home/thlinux/tmp/c2-contour51-20261108-lean432`.
- PR #304, #311, and #306 are open and mergeable; their heads were checked after `git fetch origin`. Do not modify their branches.
- C0 is committed and pushed as `96314ff` (`Docs: isolate radius-51 contour C0`).
- C1: `SigmaContour51DiskBridge.lean` packages the height-52 multiplicity exhaustion and exact radius-51 root classification. It compiled on Lean 4.32.0 with warnings-as-errors; both theorem axiom reports are `[propext, Classical.choice, Quot.sound]`. Commit `4b104771b7cc3dfbd487584b57b5bba1680e273e` is pushed. The source, successful build log, and hashes are recorded in `VALIDATION.md`.
- C2 work in progress: `SigmaContour51Residue.lean` locally contains the simple-zero logarithmic-derivative limit and a generic normalized Cauchy-coefficient lemma; `C2_RESIDUE_REDUCTION.md` records normalization and the finite integral reduction. Neither is compiled or part of the pushed branch.
- C4/C6 drafts: `SigmaContour51RationalGate.lean` locally contains the conditional normalized-integral/radius conversion, four exact-rational margins, shallow/large-window combination, and conditional wrapper for original `sigmaPadeD`. It is uncompiled and not part of the pushed branch.
- C3 is now supported by `certify_contour51_bound.py`: 512 Arb interval arcs and explicit Cauchy Taylor remainders prove `|R|<4/5` on the full radius-51 circle. `C3_ARb_CERTIFICATE.md` records the method and `evidence/C3_ARb_ARCS.csv` the per-arc enclosures. This is a rigorous computer-assisted certificate, not a Lean theorem.
- Draft PR #314 is open and stacked on B2 PR #311 (`agent/c2-central-ten-heights-b2-20261108`); it includes C1 commit `4b104771b7cc3dfbd487584b57b5bba1680e273e`. GitHub last reported it open, draft, unmerged, and `MERGEABLE`/`CLEAN`. Its description records C0/C1/C3 and the remaining C2/C4/C5/C6 obligations. Do not merge while those remain open.
- The separate C5 Lean process PID `108950` is no longer present. Before each future Lean build, recheck that no Lean/Lake process is active and use only this branch's exclusive output root.

## Next action

Commit and push the validated C1 checkpoint to the stacked draft PR. Then recheck process/memory state and compile `SigmaContour51Residue` before moving to `SigmaContour51RationalGate`; keep the Lean builds sequential. Fix errors, audit `#print axioms`, and record each checkpoint. C1 uses `RHHeight.mem_and_simple_of_Ncount_le` with the ten distinct B2 line-zero witnesses and `RHHeight.ncount_three_fiftytwo`. `sigmaContinuation_zero_re_ne_zero_of_height50` excludes a zero ordinate; `RHHeight.low_height` excludes `0 < Im ρ ≤ 3`; the height-52 count handles every positive zero through `|Re z| ≤ 51`. Reflect negative heights by evenness of the original continuation. The C3 circle estimate remains a separate Arb certificate, not imported by Lean.

Before every Lean build, check for active Lean/Lake processes; only the new output root may be written. Use the existing C2/height-52, B1, and B2 OLean artifacts read-only. Do not rebuild C2/C3 or use C5 caches.

## Source boundary

Keep `completedNativeCharacteristicContinuation` as the original continuation. It is the existing `completedRiemannZeta₀` expression under `operatorHeightParameter`; `completedNativeCharacteristicContinuation_eq_native` identifies its original native germ on the established strip. Never define `F`, `R`, or `H_n` from the zeros.

The unconditional all-order positivity target is not established by C0 or C1. B1's `hdecomp`, `he`, `hnonneg`, and `htail` remain explicit until the later checkpoints actually prove replacements.
