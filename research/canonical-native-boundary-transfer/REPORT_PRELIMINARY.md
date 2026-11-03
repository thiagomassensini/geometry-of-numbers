# Canonical native boundary transfer

## Status

This directory records the verified bridge that is actually available in the project build, and it separates it from the stronger all-order positivity claim that remains open.

## Verified in the package

The package already contains the canonical moment identity and the zero-order positivity witness for the completed native source:

- `GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalPhi_zero_pos`
- `GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalPhi_zero_ne_zero`
- `GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalLogMoment_isSequence`
- `GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalPhi_eq_normalizedEvenJet`
- `GeometryOfNumbers.Analysis.BaseTwoCompletion.baseTwoCanonicalMomentSequence_eq_logMoment`

These are the exact objects that are available in the current project tree. They certify that the canonical completion has a well-defined log-derivative moment sequence and that the leading coefficient is strictly positive.

## Open obstruction

The stronger conclusion

- canonical positivity of the completed source at all orders,
- a positive Hankel/Gram realization for the same sequence, and
- an unconditional proof that the canonical first column matches the original material clock

remains unproved in the current build.

The preserved evidence in `research/structural-native-krylov-gap` documents the obstruction explicitly:

- `finite_clock_not_canonical_firstColumn`
- `finite_clock_not_canonical_logDerivative_recurrence`
- `finite_clock_not_canonical_parityGram`
- `finite_clock_not_H6_K6`

This is not an invented counterexample; it is a formal obstruction to the realization claimed by the canonical first-column identification.

## Scope of the transfer ledger

This research note is intentionally conservative:

1. It records the proven identity and positivity that already compile under the project root.
2. It keeps the stronger all-order realization distinct from the actual package evidence.
3. It avoids claiming a theorem that is not in the package, especially the unconditional global positivity of the native source boundary energy.

The companion Lean file in this folder is the checked transfer ledger for this status.
