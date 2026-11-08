# B2 open obligations

## Scope

B2 supplies the scale-box premise `hbox` for B1 from the existing finite-height certificates and proves the genealogy of the ten roots in the original completed characteristic. It does not prove the B1 hypotheses `hdecomp`, `he`, `hnonneg`, or `htail`.

## Execution isolation

- Worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-central-ten-heights-b2-20261108`.
- Branch: `agent/c2-central-ten-heights-b2-20261108`, based on B1 PR #304 head `6397f479f8c373b59cdffea512bbd8dd95b24fb3`.
- Output root: `/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432`.
- Lean: `leanprover/lean4:v4.32.0`, warnings as errors.
- Never use or modify C5 worktrees/caches. Recheck live Lean processes before every B2 compile. Use existing C2/height-50 imports read-only; do not rebuild C2/C3.

## Remaining B2 proof work

- [x] Export the exact ten `Fin 10` witnesses and their original rational boxes through public theorem `sigmaHeight50_ten_zero_witnesses_and_count`, backed by the private `height50_*_certificate` results already in `SigmaHeight50Integration.lean`.
- [x] Convert those same heights to reciprocal-square scales and prove positivity, B1's exact rational scale boxes, `a 0 > a 1 > 0`, and a no-extra-hypothesis witness of B1's `hbox`.
- Prove the zeta-to-completed-characteristic zero and order transports at each positive height, use the even continuation for negative heights, and show the distinct-point count exhausts the height window without treating it as a multiplicity count.
- Run a transitive axiom audit for every exported theorem. Add no axioms, `sorry`, `admit`, or `native_decide` substitutes.

## Still open beyond B2

The unconditional all-window positivity remains unproved. Hadamard factorization, the ten-mode decomposition, global/refined Lehman tails, and low-index signs remain B3/B4 obligations.
