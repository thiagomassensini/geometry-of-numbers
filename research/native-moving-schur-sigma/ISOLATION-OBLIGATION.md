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

## C and D: analytic remainder and Cauchy bound, conditional on isolation

`SigmaRemainderDescent.lean` now completes the analytic bridge from B. Starting with the same
quotient `H` constructed by the isolated-zero factorization, it proves `H'(0)=0`, constructs
analytic `q` with `H'(t)=t q(t)` near zero, and removes the center singularity of
`-H'(t)/(4tH(t))`. The regularized remainder is analytic and even throughout the source `t`
disk.

The file proves the two-pole logarithmic derivative identity for the explicit factor and combines
it with `displacedProductC_local_differentialEquation`. This derives the local source identity

`G_d(t²) = sigmaZeroPairRationalModel m (τ⁻²) (t²) + sigmaDisplacedLogRemainderT H q t`.

The even Taylor coefficients are then regrouped as a power series in `u=t²`. Cauchy's estimate
proves its radius is at least `s²` for every `0<s<r_t`; choosing `s` between `|τ|` and `r_t`
places it strictly beyond the model pole radius `|τ|²`. Uniqueness of the analytic Taylor series
identifies every coefficient with the exact residual from the original `completedSigmaLogJet`
jets. Thus the existing conditional theorem's `hdecomp` and `hremRadius` are constructed inside
`completedNative_sigmaRemainder_square_decomposition_of_isolation`; they are not premises of this
source-facing theorem.

The same theorem supplies the exponential estimate
`|sigmaZeroPairRemainderMoment d m ζ n| ≤ C * η^n` with `η < ‖ζ‖`. Its radius argument uses
an intermediate `ρ` strictly between the model pole radius and the Cauchy radius. This proves
C and D under the exact source zero-set/order interface, without replacing the original
characteristic, jets, Hankel matrices, or pencil.

## Phase 7: original-pencil Padé recovery, conditional on isolation

The theorem `completedNative_sigmaRemainder_pade_root_of_isolation` feeds the derived coefficient
bound into `sigmaPadeOriginalPencil_root_tendsto_to_twoPole`. It proves that the selected root
branch of the **original sigma pencil** converges to `τ⁻²`, and that the pencil has an eventually
nonreal root together with its conjugate, which is also an original-pencil root. The conjugate
root branch converges to `conj(τ⁻²)`. The normalization to a unit-circle two-pole node is derived
from the inverse-square geometry, not assumed as extra data.

The theorem defines an explicit continuous square-root branch on the upper half-plane and proves
that the two recovered inverse-square-root height branches converge to `γ + id` and `γ − id`.
Eventually, each recovered height squares to the inverse of its corresponding original-pencil
root. No quantitative depth estimate was attempted.

## Lean audit for the published checkpoint

The continuation, isolation, remainder-descent, source-facing coefficient-bound, and Padé-root
modules compile with `-DwarningAsError=true`. `SigmaPadeAudit.lean` now includes the three new
source-facing remainder/Padé declarations in its transitive dependency audit. The audit reports
108 public roots and 59921 type/body dependencies, with only `propext`, `Classical.choice`, and
`Quot.sound`; it confirms dependencies on the original native characteristic and sigma jets. No
`sorryAx`, `admit`, new axiom, or circular continuation premise is used.

## E2: concrete certificate still open

No numerical or analytic certificate has been attached for `d=0.2` on the complete complex disk
`|u|<300` (equivalently `|t|<√300`). The exact open interface remains
`SigmaDisplacedProductIsolation`; to apply the new C/D/Padé theorem at this target, instantiate
its complex zero-set and exact product-order fields on the full `t` disk. In particular, the
certificate must rule out collisions with other shifted characteristic zeros. A critical-line
zero table or point scan is insufficient. E1 does not imply E2.

Published checkpoints before C/D: `0815c2a951ad2fd0029a5e8f158a0c8ac271e80d`,
`5304ea3`, `8696372`, and `a8926c5` on `agent/native-sigma-isolated-pole-radius`. The current C/D,
original-pencil root, conjugate-root, and height-recovery checkpoint is published as
`938f8ad0ee7ac615f7f1a983acd8ac0607d69988` on `agent/native-sigma-isolated-pole-radius`; the
remote branch was verified at that SHA. E2 remains an explicit open certificate obligation.
