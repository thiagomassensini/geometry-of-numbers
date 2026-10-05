# Ordinary/logarithmic material-gradient crosswalk

Status: `PASS_ORDINARY_LOG_GRADIENT_CROSSWALK_TFVD_MAP_OPEN`.
Initial main: `8b313f04b4106679005fc51ad5d653ada49d94e2`.

## Literal coordinates, line and sign

Set `s(t) = baseTwoDressingParameter (t : ℂ) = 1/2 + i t`.
The index `n` labels the **consecutive material edge** from `n+1` to `n+2`.
The two independent formula definitions are

\[
 g_t(n)=(n+2)^{-s(t)}-(n+1)^{-s(t)},
\]

\[
 c_t(n)=\log(n+2)(n+2)^{-s(t)}-\log(n+1)(n+1)^{-s(t)}.
\]

The local ordinary channel is literally `g_t`; the transported triangular
clock coordinate on `baseTwoCompletedBoundaryHilbertState t` is literally
`c_t`. These identities reuse the existing power-difference theorem and the
existing sample/clock-coordinate theorem. The logarithmic formula is defined
from material powers, not from a derivative. The derivative theorem then gives

\[
 \frac{d}{dt}g_t(n)=-i c_t(n).
\]

## Read-only historical comparison

Only these files at `thiagomassensini/carry-self-adjoint-operator`, revision
`62b1c0d6b18e70b4c156c3bdf0253893fdb27a35`, were consulted:

- `CarrySelfAdjointOperator/CompletedC3AllCutoffHilbertState.lean`;
- `CarrySelfAdjointOperator/C3NativeTraceDynamics.lean`;
- `CarrySelfAdjointOperator/C3SeededClockShiftIdentity.lean`.

The first file's unfolding proof of
`norm_positiveLogDirichletGradient_le` identifies its logarithmic gradient
with the difference of `realLogDirichletPower` at `n+2` and `n+1`, using
`n+1+1=n+2`. The trace file unfolds `positiveDirichletValue`,
`positiveDirichletGradient`, `positiveLogDirichletValue`,
`positiveLogDirichletGradient` in its affine-clock identity; the seed at
index zero is material 1, and its first three gradients use material
frequencies log 2, log 3, log 4. The shift file separately reconstructs the
seeded four-node block: `seededRecover_nativeBlockSeededData` identifies
seed plus successive gradients with the original values at material indices
3m+1 through 3m+4, confirming the forward-difference orientation. No such nodal reconstruction is used in the new proof.

Thus the historical positive-value index `n` means material `n+1`, and both
historical gradient indices align with the current index with **shift zero**.
The pair agrees literally in powers, material indices, line orientation and
positive log companion; the temporal derivative carries **-i**. This is a
source-formula comparison, not a Lean theorem importing historical symbols.
All new Lean equalities use explicit local formulas; no historical dependency
or certificate is added.

## Completed Hilbert pair and prefixes

`BaseTwoOrdinaryLogGradientCarrier` is the standard
`WithLp 2 (MaterialEdgeL2 × MaterialEdgeL2)`. Its state consists exactly of
`baseTwoCompletedMaterialGradientL2 t` and
`baseTwoCompletedMaterialClockL2 t`. Each is already constructed locally from
its proved ℓ¹ membership before ℓ²; ordinary ℓ¹ is named
`baseTwoCompletedMaterialGradient`, and its clock companion is
`baseTwoCompletedMaterialClockL1`. No summability estimate is reproved.

The pair has the unchanged energy

\[
 \|\mathrm{pair}_t\|^2=\|g_t\|_{\ell^2}^2+\|c_t\|_{\ell^2}^2.
\]

Direct coordinate truncations of **both difference channels** converge in this
product Hilbert norm, by `lp.hasSum_single` and product continuity.
No raw material-node limit is formed. The previous nodal harmonic-energy
no-go therefore does not exclude this pair; it remains valid for its original
nodal candidate. No claim of clock symmetry follows from this finite energy.

## Exact remaining TFVD map

The inspected local APIs are:

- `realCarryTfvdAnalysis`: a real **vertical** sequence to bracket plus two
  trace coordinates, with exact synthesis;
- `MaterialLogTfvdCanary`: externally labelled material fibers, each already
  carrying separate real-quadrature **vertical** sequences;
- `c2FiberTfvdAnalysis` / `c2OddMaterialTfvdAnalysis`: the proved C2 address
  chart `(core, direction, depth-from-two)` precedes real vertical TFVD.

None of these supplies a provenance-preserving analysis of the current
**consecutive-material-edge pair** as such. Equality of sequence index types
is not an incidence chart. In particular, no index here is silently called C2
depth, a camera code or TFVD order.

For the existing C2 fiber interface the missing input map is precisely a real
linear, geometrically specified map of the form

```lean
BaseTwoOrdinaryLogGradientCarrier →ₗ[ℝ]
  (GeometryOfNumbers.Analysis.C2RealVerticalChannels ×
   GeometryOfNumbers.Analysis.C2RealVerticalChannels)
```

with an explicit material-edge-to-C2-fiber incidence/reconstruction law, real
and imaginary quadratures, both ordinary/log channels, and retained boundary
provenance. Merely defining a map with that type is insufficient: its lossless
reconstruction and material-clock compatibility must be proved. No such map
has been constructed or assumed in this round. The present result ends before
TFVD/Green input, symmetric intertwining, moments or Krylov.

## New public declarations and audit

`BaseTwoOrdinaryLogGradientCrosswalk.lean` exposes:

- `baseTwoNativeOrdinaryGradientFormula`, `baseTwoNativeLogGradientFormula`;
- `criticalMaterialGradient_eq_nativeOrdinaryFormula`;
- `baseTwoCompletedClockCoordinate_eq_nativeLogFormula`;
- `criticalMaterialGradient_hasDerivAt_nativeLogFormula` and its `deriv` version;
- `BaseTwoOrdinaryLogGradientCarrier`, `baseTwoOrdinaryLogGradientState`;
- its ordinary/log projections and coordinate formula theorems;
- `baseTwoOrdinaryLogGradientState_norm_sq`;
- `baseTwoOrdinaryLogGradientPrefixState` and its norm-convergence theorem.

Every public declaration has `#assert_analysis_axioms` and `#print axioms`
checks in the central Analysis audit and the scoped crosswalk audit. The
allowed footprint is only `[propext, Classical.choice, Quot.sound]` (individual
declarations can use a subset). No new mathematical axiom, placeholder or trust
escape is introduced. Foundation and Geometry are unchanged.

Verification commands for this increment:

```bash
lake build --wfail GeometryOfNumbers.Analysis.BaseTwoOrdinaryLogGradientCrosswalk \
  GeometryOfNumbers.Analysis.BaseTwoOrdinaryLogGradientCrosswalkAudit \
  GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit
lake env lean GeometryOfNumbers/Analysis/BaseTwoOrdinaryLogGradientCrosswalkAudit.lean
bash scripts/audit-analysis.sh
git diff --check
```

The four `--wfail` targets, scoped kernel check, Analysis audit, placeholder
scan and `git diff --check` all completed with exit status zero. Scoped examples
also check the standard complex `InnerProductSpace` and `CompleteSpace`
instances for the bundle.

The containing commit, `feat: identify ordinary and log material gradient formulas`,
records this round atomically; its SHA is reported in the execution report.
