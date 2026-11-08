# Restart point — radius-51 contour route

## Current state

- Read the full PR #306 investigation, copied it into this branch, and reproduced its Python probe. The grid and floating-point jet values remain experimental evidence only.
- Worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108`.
- Branch: `agent/c2-contour51-20261108`.
- Base: B2 PR #311 head `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`; B1 is inherited through B2.
- Exclusive Lean output: `/home/thlinux/tmp/c2-contour51-20261108-lean432`.
- PR #304, #311, and #306 are open and mergeable; their heads were checked after `git fetch origin`. Do not modify their branches.
- C0 is committed locally after the audit record; C1 is the next proof task.

## Next action

Formalize the C1 disk-root theorem. The key multiplicity tool is `RHHeight.mem_and_simple_of_Ncount_le`, applied to the ten distinct B2 line-zero witnesses and `RHHeight.ncount_three_fiftytwo`. `sigmaContinuation_zero_re_ne_zero_of_height50` excludes a zero ordinate; `RHHeight.low_height` excludes `0 < Im ρ ≤ 3`; the height-52 count then handles every positive zero through `|Re z| ≤ 51`. Reflect negative heights by evenness of the original continuation.

Before every Lean build, check for active Lean/Lake processes; only the new output root may be written. Use the existing C2/height-52, B1, and B2 OLean artifacts read-only. Do not rebuild C2/C3 or use C5 caches.

## Source boundary

Keep `completedNativeCharacteristicContinuation` as the original continuation. It is the existing `completedRiemannZeta₀` expression under `operatorHeightParameter`; `completedNativeCharacteristicContinuation_eq_native` identifies its original native germ on the established strip. Never define `F`, `R`, or `H_n` from the zeros.

The unconditional all-order positivity target is not established by C0 or C1. B1's `hdecomp`, `he`, `hnonneg`, and `htail` remain explicit until the later checkpoints actually prove replacements.
