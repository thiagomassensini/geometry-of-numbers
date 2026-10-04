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

## Raw ℓ² readout: nonclosability

Additional status: `RAW_L2_READOUT_NOT_CLOSABLE`.
`BaseTwoRawL2ReadoutNonclosable.lean` uses the existing signed witness
`u_(N+1)` and sets `v_N = u_(N+1)/(2(N+1))`.
Its squared ℓ² norm is `1/(2(N+1))`, so it tends to zero.
For **any** partial linear operator `T` whose graph contains the coordinate
pairs `(delta_n, rawEdgeCoefficient n)`, linearity puts `(v_N,1)` in its graph.
Thus `(0,1)` belongs to its graph closure. That closure cannot be a graph of a
partial linear map, since a linear map sends zero to zero.

This is expressed using Mathlib's actual `LinearPMap.IsClosable`:
`baseTwoRawL2Readout_not_closable`. It excludes every partial extension agreeing
on all finite coordinate deltas, and hence includes the usual finite-support
raw readout. It neither requires nor constructs a new Hilbert representation.

Capstones: `baseTwoRawL2NormalizedWitness_norm_sq`,
`baseTwoRawL2NormalizedWitness_tendsto`,
`baseTwoRawL2NormalizedWitness_mem_graph`,
`baseTwoRawL2Readout_vertical_graph_limit`,
`baseTwoRawL2Readout_not_closable`.
All are independently registered in the Analysis audit and specific audit.
Commands: the same build/kernel/audit commands above, additionally targeting
`BaseTwoRawL2ReadoutNonclosable` and `BaseTwoRawL2ReadoutNonclosableAudit`.
The Hilbert boundary realization was integrated as
`4dc53afc206c3407388806082bd89bc0a36291ab` before this increment began.

## Dynamics: exact component audit, autonomous operator still open

`BaseTwoCompletedBoundaryDynamics.lean` proves the material sample derivative
`f'_t(n) = -i log(n) f_t(n)`, using its existing exponential definition.
The seed is constant. For the interior edge `g_t(j) = f_t(j+2)-f_t(j+1)`:

```text
g'_t(j) = -i [log(j+2) f_t(j+2) - log(j+1) f_t(j+1)]
        = -i log(j+1) g_t(j)
          - i [log(j+2)-log(j+1)] f_t(j+2).
```

`criticalMaterialGradient_deriv_eq_diagonalClock_add_residual` proves this
exact residual, and `baseTwoMaterialGradientDiagonalClockResidual_zeroEdge_ne_zero`
proves it is nonzero at `j=0` for every real time. Consequently the ordinary
diagonal clock reading `log(j+1)` on the edge coordinate is not its evolution
law (`criticalMaterialGradient_deriv_zeroEdge_ne_diagonalClock`). This is a
no-go for that candidate, not for every possible induced generator.

The finite reconstruction theorem already in the repo supplies the natural
coordinate formula, defined on the completed carrier before moments:

```text
K_j(seed,g,boundary)
  = log(j+2) g(j)
    + [log(j+2)-log(j+1)] (seed + sum_(k<j) g(k)).
```

`baseTwoCompletedBoundaryHilbertClockCoordinate_eq` verifies it on the
completed state. `baseTwoCompletedBoundaryHilbertInterior_coordinate_hasDerivAt`
proves each interior coordinate has derivative `-i K_j`.

`baseTwoCompletedBoundaryValue_hasDerivAt` proves the boundary derivative is
`deriv baseTwoCriticalCompleteSignal t`, using the already proved seed-plus-
return identity and signal analyticity. This is a derivative consequence, not
a new definition of the boundary.

No strong ℓ² derivative or autonomous operator on the whole product is
asserted. An operator realization would still need an exact domain for the
reconstructed interior clock, a boundary action compatible with the derived
return derivative, and strong differentiation in the product norm. These
coordinate laws do not supply those facts automatically.

All public declarations have standard-axiom guards and `#print axioms`.
The specific audit additionally checks `InnerProductSpace ℂ` and
`CompleteSpace` instances of the product carrier. All relevant `--wfail`
builds, kernel audit, and Analysis/Foundation/Geometry scripts are run for
this increment. The no-closability increment was integrated as
`df8fda9d0acdf59a40fa3e02e381fe6b7309e835` before this dynamics audit began.

## Next first-column gate

No first-column pairing has been built. The remaining moment question is to
identify geometrically a jet family `J_r` in the completed carrier such that
`baseTwoCanonicalMomentSequence r = Re(inner ℂ (J_r) (J_0))`, with the correct
normalization and dressing. Using Krylov in that question additionally needs
the autonomous generator/domain seam above. No equality of moments and vector
pairings is assumed or concluded here.
