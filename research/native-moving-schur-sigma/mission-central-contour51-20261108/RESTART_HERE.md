# Restart point — radius-51 contour route

## Current state

- Read the full PR #306 investigation, copied it into this branch, and reproduced its Python probe. The grid and floating-point jet values remain experimental evidence only.
- Worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108`.
- Branch: `agent/c2-contour51-20261108`.
- Base: B2 PR #311 head `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`; B1 is inherited through B2.
- Exclusive Lean output: `/home/thlinux/tmp/c2-contour51-20261108-lean432`.
- PR #304, #311, and #306 are open and mergeable; their heads were checked after `git fetch origin`. Do not modify their branches.
- C0 is committed and pushed as `96314ff` (`Docs: isolate radius-51 contour C0`).
- C1 draft: `SigmaContour51DiskBridge.lean` locally packages the height-52 multiplicity exhaustion and exact radius-51 root classification. It is not compiled and is not part of the pushed branch.
- C2 work in progress: `SigmaContour51Residue.lean` locally contains a generic simple-zero logarithmic-derivative limit lemma; `C2_RESIDUE_REDUCTION.md` records normalization and the Cauchy-integral reduction. Neither is compiled or part of the pushed branch.
- C4/C6 drafts: `SigmaContour51RationalGate.lean` locally contains the conditional normalized-integral/radius conversion, four exact-rational margins, shallow/large-window combination, and conditional wrapper for original `sigmaPadeD`. It is uncompiled and not part of the pushed branch.
- C3 is now supported by `certify_contour51_bound.py`: 512 Arb interval arcs and explicit Cauchy Taylor remainders prove `|R|<4/5` on the full radius-51 circle. `C3_ARb_CERTIFICATE.md` records the method and `evidence/C3_ARb_ARCS.csv` the per-arc enclosures. This is a rigorous computer-assisted certificate, not a Lean theorem.
- Draft PR #314 is open, stacked on B2 PR #311 (`agent/c2-central-ten-heights-b2-20261108`), and contains only the published C0/C3 checkpoint. Its head is `dd9c8c96d47772305067ead9f708cc4f44c114a8`; do not merge it while C1–C6 remain open.
- At the last check, a separate C5 Lean 4.32 process (PID `108950`) was still live after 1 hour 47 minutes, at 100% CPU and about 8.8 GiB RSS in its own worktree/output directory. Preserve it; recheck before any Lean build and wait until it exits.

## Next action

Open a draft PR for the committed C0/C3 checkpoint, based on B2 PR #311. Then recheck the active C5 process and compile `SigmaContour51DiskBridge`, `SigmaContour51Residue`, and `SigmaContour51RationalGate` sequentially after it exits. Fix any errors, audit `#print axioms`, and commit/push the validated C1 checkpoint before continuing with C2's finite analytic gluing and C6 validation. The C3 circle estimate is available as a separate Arb certificate, not imported by Lean. The key multiplicity tool is `RHHeight.mem_and_simple_of_Ncount_le`, applied to the ten distinct B2 line-zero witnesses and `RHHeight.ncount_three_fiftytwo`. `sigmaContinuation_zero_re_ne_zero_of_height50` excludes a zero ordinate; `RHHeight.low_height` excludes `0 < Im ρ ≤ 3`; the height-52 count then handles every positive zero through `|Re z| ≤ 51`. Reflect negative heights by evenness of the original continuation.

Before every Lean build, check for active Lean/Lake processes; only the new output root may be written. Use the existing C2/height-52, B1, and B2 OLean artifacts read-only. Do not rebuild C2/C3 or use C5 caches.

## Source boundary

Keep `completedNativeCharacteristicContinuation` as the original continuation. It is the existing `completedRiemannZeta₀` expression under `operatorHeightParameter`; `completedNativeCharacteristicContinuation_eq_native` identifies its original native germ on the established strip. Never define `F`, `R`, or `H_n` from the zeros.

The unconditional all-order positivity target is not established by C0 or C1. B1's `hdecomp`, `he`, `hnonneg`, and `htail` remain explicit until the later checkpoints actually prove replacements.
