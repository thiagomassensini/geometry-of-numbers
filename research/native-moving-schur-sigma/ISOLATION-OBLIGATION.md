# Sigma–Padé isolation work: verified results and remaining obligations

Reference checkout: `thiagomassensini/geometry-of-numbers`, base
`b7a7ca1f2a06faea539ee848bc5bdfa58507cb9c`.

Working branch: `agent/native-sigma-isolated-pole-radius`.

## Provenance and source identity

The existing Lean development preserves the source chain

`Bracket → Genuine → N → F=A·N → logarithmic response → sigma jets → Hankel → pencil`.

No source characteristic, jet, Hankel matrix, or pencil definition was replaced in this work.
Checkpoint A's source–generator identities were already present at the reference commit and
were inspected in their declarations: `displacedProductC_local_differentialEquation`,
`completedSigmaLogJet_eq_logDisplacedProduct`, and
`completedSigmaLogJet_quarter_normalization`. They identify the original jets and the local
logarithmic derivative of the original displaced product, including the factor `1/4`.

## E1: entire continuation

`SigmaNativeContinuation.lean` defines the entire continuation using Mathlib's regularized
completed zeta `completedRiemannZeta₀`. It proves analyticity everywhere, equality with the
native characteristic on the already-proved native strip, and equality of the continued and
native displaced products on a neighborhood of the origin. Mathlib's functional equation for
`completedRiemannZeta₀` also proves evenness of the continued characteristic and displaced
product. These statements establish E1 and the source-germ compatibility needed to use a
future zero certificate. They do not establish a zero-free region.

## B: conditional factorization from source zero data

`SigmaIsolationFactorization.lean` defines
`SigmaDisplacedProductIsolation d γ r m`. Its source-facing obligations are:

1. `r > 0`, `m > 0`, and the first shifted root lies in `|t| < r`;
2. `γ > 0` and `0 < d < 1/4`; Lean derives that the four signed conjugate roots are distinct;
3. throughout the **complex** disk `|t| < r`, the continued source product vanishes exactly
   at `τ`, `-τ`, `conj(τ)`, and `-conj(τ)`;
4. its exact analytic order at each of those four points is `m`.

The roots, exact orders, and local isolation of the displayed polynomial factor are proved in
Lean. From only the source zero-set and order data, the theorem constructs `H` and proves on the
disk that the continued source product equals

`(1 - t²/τ²)^m (1 - t²/conj(τ)²)^m H(t)`,

where `H` is analytic, nowhere zero, and even. The constructed quotient is not an input to the
certificate. `displacedProductC_native_germ_factorization_of_isolation` additionally packages
the same factorization as an eventual equality for the original `displacedProductC` on the
native admissible displacement range. This proves B conditionally on explicit source zero data.

The order data is an order of the *product*. If the target factor has order `m` and the other
shifted factor also vanishes, analytic-order additivity raises the product order above `m`, so
the certificate cannot be instantiated with the target multiplicity. The numerical certificate
must consequently establish noncollision as well as the exact product orders; the current Lean
interface does not silently infer the order of either shifted characteristic factor.

## E2: exact open certificate

No rigorous certificate for `d = 0.2`, `|u| < 300` was found or produced here. E1 alone says
nothing about this obligation. The radius-300 claim requires a proof over the full complex
`t` disk `|t| < √300`, not a list of critical-line zeros or a point scan.

The exact Lean interface is `SigmaDisplacedProductIsolation`. To instantiate it at this target,
the missing external evidence must prove `source_zero_set` for every complex point in that disk
and `source_order` with the same multiplicity at all four roots. A viable argument-principle
certificate would need a verified nonvanishing bound on a contour enclosing the disk and a
rigorous winding-number/zero count for the continued product, together with exact local orders
at the four roots. No such contour data, interval arithmetic proof, or equivalent analytic
certificate is currently attached.

## C, D, and convergence application: still open

The B theorem does not yet construct the required function of `u = t²` from
`-H'(t)/(4tH(t))`. This work has not proved its removable singularity at zero, its holomorphy
as a function of `u` on a disk larger than `|τ|²`, or equality of its coefficients with
`completedSigmaLogJet d n - m * Re(τ^(-2n-2))`. It has therefore not eliminated `hdecomp` or
`hremRadius` in `SigmaZeroPairDecomposition.lean`.

Consequently there is no new exponential Cauchy bound for the original coefficient remainder
and no new application of the existing conditional Padé convergence theorem to the native
source. The existing Padé, Schur, pencil, and conditional convergence results remain intact and
conditional. Quantitative depth estimates were not attempted.

## Lean audit for the published checkpoint

The two new Lean modules compiled with `-DwarningAsError=true`. Axiom reports for the new public
continuation, polynomial-root/order, quotient, and factorization theorems contain only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, `admit`, or new axiom is used.

Published commit: `0815c2a951ad2fd0029a5e8f158a0c8ac271e80d` on
`agent/native-sigma-isolated-pole-radius`.
