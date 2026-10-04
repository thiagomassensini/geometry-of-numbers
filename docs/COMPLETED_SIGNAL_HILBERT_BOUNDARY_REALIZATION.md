# Completed signal: Hilbert interior and explicit geometric boundary

## Question and result

`PASS_COMPLETED_SIGNAL_HILBERT_BOUNDARY_REALIZATION`.
Can the complete signal be read boundedly after geometric synthesis, even
though the raw edge sum has no bounded extension to the ordinary ℓ² interior?
Yes: the previously proved complete-cell returns supply an explicit boundary
coordinate. This does not extend that raw functional.

## Carrier and causal order

`BaseTwoCompletedBoundaryHilbertCarrier` is the standard Hilbert sum
`ℂ ⊕ (ℓ²(ℕ, ℂ) ⊕ ℂ)`, implemented with nested `WithLp 2` products.
No modified metric or chosen weights are used. The components are material
seed, material-edge gradient interior, and total complete-cell return.
Material-edge indices are not C2 vertical depths.

The finite states store the existing seed, `baseTwoCompletedMaterialInteriorPrefix N t`,
and `baseTwoCompletedBoundaryPrefix N t`. The same cutoff labels two distinct
prefixes: material edges and complete cells. It does not identify those indices.
The completed state stores the existing ℓ² gradient and
`baseTwoCompletedBoundaryValue t`. That boundary was already defined by the
sum of whole-cell edge returns and proved to be their prefix limit. Its primary
definition is not signal minus seed.

`baseTwoCompletedBoundaryHilbertPrefixState_tendsto` proves convergence in the
product Hilbert topology from the two existing convergence theorems.
The component projection theorems expose all three coordinates.

## Bounded readout and exact observable

`baseTwoCompletedBoundaryHilbertReadout` is a complex continuous linear map,
`beta(seed, interior, boundary) = seed + boundary`. It reads the explicit
finite-dimensional boundary; it does not sum coordinates of the ℓ² interior.

- `baseTwoCompletedBoundaryHilbertPrefixState_readout`: each finite readout is
  the existing geometric finite head.
- `baseTwoCompletedBoundaryHilbertReadout_eq_signal`: the complete readout is
  exactly `baseTwoCriticalCompleteSignal`, by the previously proved
  seed-plus-derived-return identity.
- `baseTwoCompletedBoundaryHilbertReadout_eq_banachReadout`: the previous Banach
  lift has the same observable. No equivalence or isometry of carriers follows.
- `baseTwoCompletedBoundaryHilbertPrefixState_readout_tendsto`: bounded readout
  carries prefix convergence to the complete signal.

## Limits of the result

No generic graph lift `(x, ell(x))` from ℓ² is constructed. The boundary is
synthesized from the actual geometric returns of this family. The existing raw
ℓ² no-go remains valid. No identification with TFVD initial trace is asserted.
No autonomous generator, strong vector derivative, moment pairing, Gram,
Hankel positivity, or height operator follows from this construction.

The next first-column gate is to identify a geometrically derived jet family
and pairing on this completed carrier whose first column is the canonical
moment sequence. Equality of scalar readouts alone does not prove that gate.

## Provenance and verification

Local sources: `BaseTwoCompletedBoundaryLimit.lean`,
`BaseTwoCompletedGradientSignalLift.lean`, and
`BaseTwoRawL2ReadoutObstruction.lean`. No historical package is imported.
Standard Hilbert product and continuous projection APIs come from Mathlib.
All public declarations are checked in the central Analysis audit and the
specific module audit. Allowed transitive axioms are `propext`,
`Classical.choice`, and `Quot.sound` only.

Verification commands for this increment:

```bash
lake build --wfail GeometryOfNumbers.Analysis.BaseTwoCompletedBoundaryHilbert
lake build --wfail GeometryOfNumbers.Analysis.BaseTwoCompletedBoundaryHilbertAudit
lake build --wfail GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit
lake env lean GeometryOfNumbers/Analysis/BaseTwoCompletedBoundaryHilbertAudit.lean
bash scripts/audit-analysis.sh
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
git diff --check
```

Initial main: `a0e4dff8e296c90ae382036d5bb8d52d245a3e13`.
The integration commit is the commit introducing this document and module.
