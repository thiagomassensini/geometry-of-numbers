# Transported material clock in seeded gradient and boundary coordinates

## Question and first increment

The original material clock reads `log n`. Changing samples to seed and
consecutive material differences produces a causal triangular clock, not a
new fitted operator. A linear similarity is not automatically unitary.
The standard Hilbert product metric must therefore be tested separately.

Initial canonical main: `d9ccecb8b2c8240d68c2874d544f0e2bd8b8150c`.
All proofs use local geometry-of-numbers and Mathlib APIs. No historical
certificate, moment, Hankel, Jacobi, height, or positivity premise is used.

## Exact finite coordinate transport

`FiniteSeedGradientClock.lean` uses the existing
`FiniteRealSpectralHilbert (K+1)` of material samples and the standard Hilbert
product `FiniteSeedGradientCarrier K = ℂ ⊕ EuclideanSpace ℂ (Fin K)`.

- Encode: seed `x(0)` and edge `x(j+1)-x(j)`.
- Decode: sample `j` is seed plus the sum of preceding edges.
- `finiteSeedGradientDecode_encode` and `finiteSeedGradientEncode_decode`
  prove both roundtrips.
- `finiteSeedGradientEquiv` packages this **linear**, not isometric, equivalence.

`baseTwoCell_materialCutoff` derives from the existing C2 left/right edge
indices that N complete cells fit into exactly `4N` edges and material samples
`1,...,4N+1`. The last right edge is `4N-1` when N is positive. These are material
edges, not vertical carry-depth coordinates.

## Clock and finite strong derivative

`finiteSeedGradientClock K = Encode ∘ finiteMaterialClock (K+1) ∘ Decode`.
Its seed coordinate is zero and its gradient coordinate is

```text
log(j+2) g_j
+ [log(j+2)-log(j+1)] (seed + sum_(k<j) g_k).
```

`finiteSeedGradientClock_gradient` derives that formula from conjugation.
`finiteSeedGradientClock_intertwining` proves exact transport of the existing
material generator.

`finiteMaterialOrbit_hasDerivAt` and `finiteSeedGradientOrbit_hasDerivAt`
prove strong finite-dimensional differentiation, including the factor `-i`:
`Y'_K(t) = -i L_grad,K Y_K(t)` for the existing material orbit followed by Encode.
The derivative generator `-i L` is not called self-adjoint.

## Metric kept explicit

`finiteSeedGradientMaterialPairing K x y` is
`inner ℂ (Decode x) (Decode y)`. Its symmetry identity for the transported
clock follows from the existing material-clock symmetry. This is a recorded
pullback pairing, not a replacement instance for the standard Hilbert metric.
Its quadratic form is the sum of squared reconstructed samples:

```text
sum_(j=0,...,K) |seed + sum_(k<j) g_k|².
```

No equality with the standard product norm or an existing TFVD energy has
been asserted. At this increment, finite boundary graph invariance and
standard-metric symmetry still need their own proofs. Infinite operator/domain,
strong Hilbert differentiation, and summed boundary clock also remain open.

## Verification

All public names enter `Analysis/Audit.lean` with the standard-axiom guard and
`#print axioms`, and a module-specific audit is provided. Each increment runs:

```bash
lake build --wfail GeometryOfNumbers.Analysis.<module>
lake build --wfail GeometryOfNumbers.Analysis.<module>Audit
lake build --wfail GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit
lake env lean GeometryOfNumbers/Analysis/<module>Audit.lean
bash scripts/audit-analysis.sh
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
git diff --check
```

No new axiom or trust escape is permitted. Analysis capstones allow only
`propext`, `Classical.choice`, `Quot.sound`; foundation and geometry retain
separate audits. Every validated increment is integrated and pushed on main
before the next mathematical increment.

## Finite whole-cell boundary graph and metric witness

`FiniteCompletedBoundaryClock.lean` keeps the boundary redundant:
`finiteCompletedBoundaryGraph N` is the range of
`finiteCompletedBoundaryEmbed N`, equivalently `b = B_N(g)`.
Here `B_N(g)` sums right-minus-left material edge coordinates over the first
N complete C2 cells. The graph clock is the core transported clock followed
by this same embedding. Its boundary action is therefore exactly the sum of
clocked cell returns; no extension on an independent ambient boundary is made.

`finiteCompletedBoundaryOrbit_hasDerivAt` proves the strong graph-valued orbit
equation with factor `-i`. `finiteCompletedBoundaryOrbit_historical_boundary`
identifies the existing historical finite material orbit's boundary with the
already defined geometric prefix. The boundary derivative is explicitly the
sum of clocked right-minus-left edges.

`finiteCompletedBoundaryClock_not_standard_symmetric` excludes symmetry in the
standard product Hilbert metric already for one complete C2 cell. Transport
material deltas at 1 and 2: their graph inner product is -1, but their clock
eigenvalues are 0 and log 2. Symmetry would force their inner product to vanish.
The witness uses the actual boundary graph; it does not test an arbitrary
extension to the full product.

Thus the transported clock is correct, while the standard seed-gradient-boundary
metric does not preserve material-clock symmetry. The recorded pullback pairing
in the first increment does preserve symmetry, but no equality with TFVD/Green
energy has been proved and no metric instance was changed. The infinite
operator/domain and strong differentiation remain separate gates.

First increment, published and reference-verified before the second:
`02d24b2e8f7fa51ecbc022169e5451a9127a3845`.

## Strong infinite gradient and geometric boundary derivative

`CompletedMaterialGradientStrongClock.lean` proves strong differentiability of
the preexisting gradient orbit both in standard ℓ¹ and standard ℓ². It first
bounds complex-time material first differences uniformly near each real time:
`norm ≤ (|t|+2) (j+1)^(-5/4)`. This summable bound controls the series of coordinate
vectors `lp.single`, not just scalar coordinates. Mathlib's Banach-valued
holomorphic normal-series theorem gives strong differentiability; restriction
to the real time line recovers the existing material gradient exactly.
This legitimate material-sample continuation is not the refuted normalized
complex Taylor product-ledger candidate, and it supplies no moment Gram.

Only after this norm-level proof, bounded coordinate evaluation and derivative
uniqueness identify the strong derivative with `-i C_j(Y(t))`. Absolute
summability of the triangular coordinates follows from the strong ℓ¹ derivative.
`baseTwoCompletedMaterialClockL1/L2` package those preexisting coordinates;
the operator formula is not defined from a fitted derivative.

The actual clocked cell series is
`sum_k (C_rightEdge(k)(y)-C_leftEdge(k)(y))`, named
`baseTwoCompletedBoundaryClockReturn`. On the concrete completed orbit it is
summable. `baseTwoCompletedBoundaryValue_hasDerivAt_clock` derives the boundary
derivative from the existing bounded ℓ¹ whole-cell return readout composed with
the strong gradient derivative. It does not define the boundary clock via `S'`.
The previously proved signal-based derivative theorem is preserved.

No material edge is identified with vertical depth. No claim is made that an
arbitrary CoreState is in a material-log domain. This concrete gradient orbit
has its own norm-level summability proof. The remaining operator step is to
package the triangular coordinates and summed boundary return on a natural
partial domain, retaining the geometric boundary graph.

Finite graph and standard-metric no-go published in
`318ee32070224a82cba5fb936867bd4a2e97af90` before this increment.
