# Synthesis before scalarization: base-two clock coefficients and moments

Initial main: `fd3216eb4b908507070ca856d6dc990ea59683c3`.
Branch: `base-two-synthesized-clock-moments`.

## Question and causal order

Can the exact base-two synthesis determine its entire normalized coefficient
tower, derive the tail coefficients, and feed the existing formal logarithmic
moment ledger without a freely supplied tail?

The normative order is provenance → complete cells → exact head/tail synthesis
→ normalized jets/readout → logarithmic derivative → moments.
A mismatch for a prematurely scalarized representation is not an impossibility
theorem about the complete theory. This round does not identify the historical
material amplitude n^(-1/2) with the modern C2 depth amplitude 2^(-k/2).

## Block 1: normalized coefficients AFTER synthesis

Module: `BaseTwoSynthesizedClockCompletion.lean`.
Status: `PASS_DERIVED_TAIL_JETS` (coefficient-level result).

The already-proved `baseTwoFiniteHead_add_completeTail` gives equality of entire
functions. `baseTwoSynthesizedSignal_eq_complete` records that equality, then
`baseTwoSynthesizedSignal_iteratedDeriv` rewrites it at every order and time.
No head/tail identity is reproved and no derivative/tsum interchange is used.

The coefficient is defined from the complete signal:

$$
c_r=(r!)^{-1}\,\operatorname{iteratedDeriv}_r(\mathrm{Signal})(0).
$$

`baseTwoCompletedClockJet_cutoff_independent` proves all-order independence of
the cutoff at this interface. The convention includes the existing factorial,
rotation and real temporal parameter; it is not a raw-derivative convention.

Only after synthesis and jet extraction is the tail defined:

$$
\tau_{M,r}=c_r-\mathrm{historicalFiniteHeadCoefficient}_{M,r}.
$$

`baseTwoHeadCoefficient_add_synthesizedTailCoefficient` certifies the exact sum.
`baseTwoSynthesizedTailCoefficient_eq_jetResidual` connects it to the unchanged
`baseTwoFiniteHead_normalizedClockJet`. At order zero,
`baseTwoSynthesizedTailCoefficient_zero` identifies it with the geometric tail
value already proved in the previous round.

`baseTwoSynthesizedTailSeries` is `PowerSeries.mk` of these derived residuals.
`baseTwoHeadSeries_add_synthesizedTailSeries` gives exactly the complete
coefficient series. `baseTwoSynthesizedTailSeries_unique` proves uniqueness
relative to the fixed head and complete coefficient series.

## Scope and gates

These are identities of the existing `iteratedDeriv` coefficient construction.
They alone do not assert analytic recovery of the infinite complete signal
from its Taylor series, smoothness of that signal, or interchange of derivatives
with the infinite cell sum. No smoothness premise was added to obtain them.
Such a regularity certificate must be proved before making those stronger claims.

The camera-factor and completion germs have not been derived in this block.
The modern provenance-correct C2/Green source → historical complete scalar
observable seam, dressing seam and positive global Gram seam remain open.
No positivity, Jacobi or height result is used retroactively here.
The existing `externalTail_changes_phi_zero` guardrail is unchanged: a freely
supplied tail is still able to change phi; a tail derived from fixed synthesis
has no such independent freedom.

## Read-only historical blueprint

Repository: `thiagomassensini/carry-self-adjoint-operator`.
Exact revision: `62b1c0d6b18e70b4c156c3bdf0253893fdb27a35`.
File: `CarrySelfAdjointOperator/C2GeometryNativeSourceBridge.lean`.
SHA-256: `acdb8d67ba096275bedb85c436b8945187374a596425458b22cf7e339cfe3217`.

The consulted `canonicalC2Geometry_completedPackagedNativeJet_eq_head_add_exactTail`
uses equality of functions followed by rewriting `iteratedDeriv`.
The camera-normalization and canonical-moment theorems in that file are
historical evidence only; their conclusions and imports are not transported.
All new proofs use GeometryOfNumbers and its existing Mathlib dependency.

## Audit / publication

Every public definition/theorem is guarded in both the dedicated and central
Analysis audits, with `#print axioms`. Allowed footprint is only
`propext`, `Classical.choice`, `Quot.sound`.

Validation commands for each mathematical block:

```bash
lake build --wfail GeometryOfNumbers.Analysis.BaseTwoSynthesizedClockCompletion
lake build --wfail GeometryOfNumbers.Analysis.BaseTwoSynthesizedClockCompletionAudit
lake build --wfail GeometryOfNumbers.Analysis
lake build --wfail GeometryOfNumbers.Analysis.Audit
bash scripts/audit-analysis.sh
git diff --check
```

Each validated block is committed, branch-pushed, immediately integrated into
main, main-pushed and checked against `origin/main` and the GitHub remote.
The publication ledger is filled with the mathematical commit SHAs after each
integration. Foundation, Geometry, R2 and dependency configuration are unchanged.


## Block 2: derived-tail ledger and unique formal moments

Module: `BaseTwoSynthesizedClockMoments.lean`.

The new `baseTwoClosedResponseSeries M cameraFactor completion` specializes
exactly the existing ledger with `baseTwoSynthesizedTailSeries M`.
`baseTwoClosedResponseSeries_eq_synthesized` proves

$$
\mathrm{Response}_M=A\,(\mathrm{CompleteClockSeries}\,B^{-1}).
$$

It follows that the response and `baseTwoHistoricalPhi` do not depend on the
cutoff when the SAME cameraFactor and completion are held fixed.
`baseTwoSynthesizedPhi` is the cutoff-free canonical real-even extraction:
$\phi_r=\operatorname{Re}([t^{2r}]\mathrm{Response})$, preserving $u=t^2$.
`baseTwoSynthesizedPhi_coefficient_formula` records the complete normalized
jet convolution with the two explicit dressing germs.

`baseTwoSynthesizedLogMoment` reuses `finiteLogMoment` without a tail input.
`baseTwoHistoricalLogMoment_eq_synthesized` and
`baseTwoSynthesizedLogMoment_cutoff_independent` identify every cutoff ledger
with that same sequence. These equalities are unconditional identities of the
existing total definitions; they are not unconditional log-derivative existence.

The existing normalization gate $\phi_0\ne0$ is required for:

* `baseTwoSynthesizedLogMoment_isSequence`;
* `baseTwoSynthesizedLogMoment_unique`;
* `baseTwoSynthesizedLogMoment_formal_logDerivative`, $H\Phi=-\Phi'$;
* `baseTwoSynthesizedLogMoment_formal_quotient`, $H=-\Phi'\Phi^{-1}$;
* `baseTwoSynthesizedLogMoment_unique_of_formal_identity` and
  `baseTwoLogMoment_two_formal_constructions_eq`.

These proofs compose the unchanged `finiteLogMoment_isSequence`,
`finiteLogMoment_eq_existing`, `IsLogDerivativeMomentSequence.unique` and
formal quotient/derivative theorems. No positive Gram hypothesis is used.
`baseTwoSynthesizedLogMoment_depends_only_on_phi` states the exact dependency.
The camera quotient separately retains its existing $B(0)\ne0$ gate.

### What has changed, and what remains

A freely supplied tail disappears completely from this NEW base-two response
and moment path. The general historical ledger and its arbitrary-tail guardrail
remain unchanged. CameraFactor and completion are still explicit external
inputs, and no identification of them with physical completed dressing was
proved. Different dressing germs may change phi and moments.

The historical scalarization mismatch is reduced only at the head/tail and
formal coefficient seam. It remains active at the modern provenance-correct
C2/Green source → historical observable/dressing seam. An early scalar mismatch
is not promoted to a no-go of the complete theory.
Regularity/Taylor recovery of the complete infinite signal remains a distinct
gate at this point; the coefficient identities alone do not discharge it.

## Publication ledger

| Block | Mathematical commit | Integrated main / origin / GitHub | Validation |
| --- | --- | --- | --- |
| 1 — synthesized jet residual and derived tail series | `9c7731b3bcb53d00530a4db6fbae2016104e9bdb` | identical, verified before block 2 | four --wfail targets + Analysis audit + diff check, exit 0 |

The next mathematical commit is recorded after its immediate integration.
