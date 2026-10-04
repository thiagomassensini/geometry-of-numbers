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
