# Correlated C3 coefficient gate

## A. Origin and provenance

This checkpoint continues branch `agent/c3-cofactor-correlation-gate-20261112`,
based on `de8f044d78260fd4ba9f728c3bb313adfa0255df` (the merged PR #322 base).
It uses the original completed C3 characteristic, C3/48 head and boundary,
original completion multiplier, native Gamma factor, and the finite coefficient
candidate balls already present in `research/c3-cofactor-chiral-certification/`.
No source, completion factor, phase, chart, scale, or cutoff was changed.

The source crosswalk reuses `GammaHeadCrosswalk.lean`,
`C3CompletionTail48.lean`, `GammaThirteen.lean`, `IntervalGate.lean`, and
`SourceGate.lean`. The coefficient computation keeps the common `log(pi)`
variable through the normalized polynomial instead of treating occurrences in
different coefficient expressions as independent inputs.

## B. Results proved in Lean

- `normalized_outer_completed_jet_eq_polynomial` expresses the completed
  normalized jet as a finite polynomial in the shared chart variables.
- `normalized_outer_completed_polynomial_box_contains` and
  `normalized_completed_reference_box_contains` transport exact rational boxes
  through the original finite head and completion calculation.
- `left_real_jet48_abs_bound` gives per-order correlated bounds, and
  `left_real_jet48_abs_sum_le_half` proves the sum of the thirteen absolute
  bounds is at most `1/2`.
- `completed_tail48_jet_error_tight` bounds the original C3/48 tail jets through
  order twelve by `2 * 10^-24`.
- `completed_native_jet_reference_error48_tight` combines the original tail
  bound with the Gamma replacement ledger and gives a total coefficient error
  at most `3 * 10^-24`.
- `native_even_finite_reference_box_subset_table` checks the emitted finite
  reference coefficient table in Lean. `native_even_coefficient_candidate_contains`
  then proves that every native even coefficient `c_0,...,c_6` lies in its
  pre-existing candidate ball.
- `completed_native_odd_third_block_posDef` applies the pre-existing conditional
  source gate to those proved coefficient boxes and certifies the original odd
  3-by-3 source block as positive definite.

These claims are finite-order source certificates. They do not identify a new
inner product and do not assert positivity of the even third block or of either
all-order tower.

## C. Correlated coefficient enclosure

The exact rational interval propagation starts from the existing chart, Gamma,
and head boxes. The normalized outer completion is evaluated as a polynomial
in one shared `log(pi)` interval; all products, sums, and reciprocal recurrences
are outward rounded and their containment steps are checked by Lean.

The chosen simple absolute bounds on the thirteen left-head jets sum to
`0.477875209124133681767793521419955867`, which is below `1/2`. The exact
Gamma replacement budget is at most `0.5 * 10^-24`; the C3/48 order-twelve tail
bound is below `1.598653 * 10^-24` and is weakened in Lean to `2 * 10^-24`.
Their sum is below the `3 * 10^-24` transport allowance used to shrink the
candidate coefficient balls. The smallest rational slack in the finite table
against that shrunken gate remains positive.

## D. Finite source result

The seven original completed coefficients lie in the candidate intervals used
by `SourceGate.lean`. Feeding these intervals into its exact cofactor margin
proves the odd 3-by-3 source block positive definite. This proof depends on the
geometric C3/48 head, the original completion and Gamma factors, and the
original C3/48 tail estimate. It does not use a Hankel/theta positivity theorem
as a sign premise.

## E. Finite-sector status

- Odd third block (`s = 1`, size 3): **GREEN** for the source block proved by
  `completed_native_odd_third_block_posDef`.
- Even third block (`s = 0`, size 3): **NOT CERTIFIED HERE**. This checkpoint
  does not claim its coefficient margin or pivot sign.
- All-order positivity of either tower: **OPEN**.

## F. Limitations

The exact interval method certifies only coefficients through `c_6` and the
odd 3-by-3 block whose conditional gate was already formalized. It does not
establish the even third pivot, a general last-coefficient law, or an all-order
source inequality. The algebraic equivalence between source and Hankel blocks
does not itself supply any missing sign.

## G. Remaining obligation

The next minimal mathematical task is to build and independently certify the
corresponding even-sector third-direction margin from the original C3 source,
without importing theta positivity as a premise. The all-order sign problem
remains separate.

## H. Validation and audit

`bash research/c3-cofactor-correlation-gate/validate.sh` compiles the research
modules explicitly with Lean 4.32.0 and `-DwarningAsError=true`, runs both exact
rational Python diagnostics, and checks `git diff --check`. It passed after the
module split and coefficient gate were added.

The repository root checks also passed: `lake build --wfail` (8,850 jobs),
`bash scripts/audit-foundation.sh`, `bash scripts/audit-geometry.sh`, and
`bash scripts/audit-analysis.sh`. The analysis audit uses the project's
standard foundational axioms; it is not an axiom-free audit.

The `#print axioms` audit for the tight tail theorem, tight native-jet error,
coefficient inclusion, and final odd-block result reports only the accepted
foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`,
`admit`, `native_decide`, or new axiom is used. The finite table is rechecked by
Lean with `decide +kernel`; Python output is used only to emit candidate rational
endpoints and diagnostics.
