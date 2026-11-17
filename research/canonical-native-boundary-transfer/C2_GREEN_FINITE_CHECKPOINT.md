# C2 finite Green sign — checkpoint

## Branches and dependency direction

- Geometry of Numbers worktree: `luna/c2-green-finite-331-20261116`, based on
  the open #331 branch `codex/luna-g-c2-sign-transport-2026-11-14`.
- Carry dependency: `luna/c2-jordan-green-unifier-20261116`, based on the
  open #119 branch, which is stacked on #118.
- The import direction is Geometry of Numbers → Carry. There is no reverse
  dependency and no import cycle.
- Neither #331, #119, #118, nor the new follow-up was merged during this work.

## New declarations

In `CanonicalBoundaryTransfer.lean`:

- `nativeSourceSchurPivot_pos_of_order_le_five`: both canonical Schur pivots
  are strictly positive for `n ≤ 5`, by applying the H6/K6 pair at size
  `n+1 ≤ 6` and the finite Schur complement equivalence.
- `nativeSourceSchurRemainder_pos_of_order_le_five`: the matching native
  Schur remainder is positive, using `c₀ > 0`.
- `nativeCriticalGreenPositive_of_order_le_five`: for either sector and every
  `n ≤ 5`, the complete theta-Green integral of the Schur source polynomial
  is strictly positive. It obtains the enlarged prefix of size `n+1 ≤ 6`
  from `canonical_hankel_pair_posDef_of_le_six` and applies the Carry
  conditional Green-sign theorem.
- `nativeSchurEuler_even_integral_pos_of_order_le_five`: the even Euler
  integral is strictly positive for `n ≤ 5`.
- `nativeSchurEuler_odd_compensation_of_order_le_five`: the odd integral
  satisfies `-2*c₀*ρ_n² < I_(1,n)` for `n ≤ 5`.

These are finite consequences of the existing H6/K6 certificate. They add no
assumption of all-order positivity and establish no order-uniform margin.
They certify integrated signs only; they do not claim pointwise positivity of
the Green density.

## Validation

- Compiled `CanonicalBoundaryTransfer.lean` with
  `bash research/canonical-native-boundary-transfer/compile_module.sh
  CanonicalBoundaryTransfer /home/thlinux/worktrees/luna-c2-euler-geometric-sign-20261116`.
- Compiled `Audit.lean` with the same script and Carry worktree.
- `#print axioms` for all five new theorems reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `compile_module.sh --check` confirmed all Geometry of Numbers and Carry
  dependency oleans were present.

## Exact gap remaining

Orders `n ≥ 6` still need a new source-side margin. The finite H6/K6
certificate gives the first six Schur pivots and Green integral signs, but
the all-order control of the signed Euler/physical Jordan balance remains
open. In particular, the C2 tail limit alone does not prove relative
dominance of the negative Jordan channel.

## Publication metadata

- GoN commit: `5af5ebe6ec692b439d9657eeebf53a4af467f20e`.
- GoN branch: `luna/c2-green-finite-331-20261116`.
- GoN draft PR #333: https://github.com/thiagomassensini/geometry-of-numbers/pull/333,
  stacked on #331 (base `codex/luna-g-c2-sign-transport-2026-11-14`).
- Carry dependency commit: `9f0d2d979c532c3a5efe2ff64a4c2b88d58196ce`.
- Carry branch: `luna/c2-jordan-green-unifier-20261116`.
- Carry draft PR #126: https://github.com/thiagomassensini/carry-self-adjoint-operator/pull/126,
  stacked on #119 (which depends on #118).
- Neither branch has been merged. PR #331 remains open.
