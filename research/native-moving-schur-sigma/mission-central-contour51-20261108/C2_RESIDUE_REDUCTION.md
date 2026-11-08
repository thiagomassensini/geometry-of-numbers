# C2 radius-51 contour identity: normalization and formalization reduction

## Original-source normalization

Write `F` for `completedNativeCharacteristicContinuation`. The existing source chain fixes the
normalization without defining moments from zeros:

1. `CarrySigmaSource.sigma_log_jet_center_eq_canonical` proves, for every `n`,
   `completedSigmaLogJet 0 n = canonicalCompletedNativeLogDerivativeMoment n`.
2. Carry's `completedNativeGreenResponseTaylorCoefficient_odd_eq_canonical` identifies that
   canonical moment with the Taylor coefficient of order `2*n+1` of the completed Green response.
3. `completedGreenNormalizedResponse F Psi z = Psi z / (2*F z)`, and
   `completedNativeOperatorBoundaryCompanion_eq_neg_deriv` identifies `Psi` with `-F'`.
4. `completedNativeCharacteristicContinuation_eq_native` identifies the entire continuation with
   the original native completed characteristic throughout the genuine strip. Since the origin
   is interior to that strip, the two analytic characteristics, their derivatives, and their
   nonvanishing logarithmic derivatives agree as germs at zero.

Thus the coefficient of `z^(2*n+1)` in the original central response
`R(z) = -F'(z)/(2*F(z))` is exactly `H_n = completedSigmaLogJet 0 n`. The factor `1/2` and the
sign are both accounted for. This identification is local at the center, where `F(0) ≠ 0`; the
contour expression uses the already-defined entire continuation, not a zero-defined source.

## Residue calculation and orientation

Let `a_j = gamma_j^(-2)`, `k = 2*n+2`, and suppose the C1 theorem supplies exactly the simple
zeros `±gamma_j` in `|z| ≤ 51`, with no zero on the radius-51 circle. Then:

- At the origin, `R(z)/z^k` has residue `H_n` by the Taylor-coefficient identity above.
- At each simple zero `alpha = ±gamma_j`, the logarithmic derivative has principal part
  `-1/(2*(z-alpha))`. Multiplying by `z^(-k)` gives residue
  `-1/(2*alpha^k)`. The pair contributes `-gamma_j^(-2*n-2) = -a_j^(n+1)`.
- The positively oriented circle `∮ z in C(0,51)` therefore gives
  `((2*pi*I)^(-1) * ∮ R(z)/z^k dz) = H_n - sum_j a_j^(n+1)`.

The sign is for the standard positive orientation used by Mathlib's `circleIntegral`.

## Concrete Cauchy reduction

A direct residue theorem is not needed. Define, away from the listed zeros,

```text
G(z) = R(z) + (1/2) * sum_{alpha in {+gamma_j,-gamma_j}} 1/(z-alpha).
```

At every listed simple zero, analytic order one gives a local factorization
`F(z) = (z-alpha)*g_alpha(z)` with `g_alpha` analytic and nonzero at `alpha`. Consequently,
`R(z) + 1/(2*(z-alpha))` agrees on the punctured neighborhood with
`-g_alpha'(z)/(2*g_alpha(z))`, which is analytic there. C1's exhaustive root classification then
shows that the finite sum `G` has an analytic extension across all twenty roots on the closed
radius-51 disk.

The compiled Lean modules package the simple-zero limit giving residue `-1/2`, a single-root
cancellation lemma that constructs an analytic extension of
`R(z) + 1/(2*(z-alpha))` from the order-one factorization, and Mathlib's normalized Cauchy
derivative formula for a regular function. `SigmaContour51FiniteContour.lean` additionally proves,
by induction on `k`, that each partial-fraction kernel
`(z-alpha)^(-1) * z^(-k)` has zero radius-51 circle integral for `k ≥ 1`, whenever `alpha` is
nonzero and inside the circle. Its `#print axioms` output is `[propext, Classical.choice,
Quot.sound]`. The successful build and source/OLean/log hashes are recorded in `VALIDATION.md`.
The helper proves the individual kernel calculation; it does not yet build the analytic extension
of the global finite correction or assemble the full identity.

For `k ≥ 2` and `0 < |alpha| < 51`, partial fractions give

```text
1 / ((z-alpha) * z^k)
  = alpha^(-k)/(z-alpha) - sum_{j=1}^k alpha^(-(k-j+1)) / z^j.
```

The integral of this expression around the radius-51 circle is zero: the `j=1` term cancels the
integral of `alpha^(-k)/(z-alpha)`, and all `j>1` powers integrate to zero. These are covered by
Mathlib's `circleIntegral.integral_sub_inv_of_mem_ball` and
`circleIntegral.integral_sub_zpow_of_ne`. The Cauchy integral formula for derivatives then
computes the integral of `G(z)/z^k` from the `(k-1)`st Taylor coefficient of `G` at zero. The
Taylor coefficient of the added finite principal-part sum is `-sum_j a_j^(n+1)`, so this
coefficient is `H_n - sum_j a_j^(n+1)`.

## Exact remaining Lean work

The current Lean 4.32 Mathlib sources provide Cauchy integral formulas and the power-kernel circle
integrals above, but a search of `Mathlib/Analysis/Complex` and `Mathlib/Analysis/Meromorphic`
found no general finite-residue theorem to apply directly. `SigmaContour51Residue.lean` and
`SigmaContour51FiniteContour.lean` compile on Lean 4.32.0 with warnings-as-errors; their theorem
axioms are `[propext, Classical.choice, Quot.sound]`. The individual partial-fraction kernel
integral is now proved. The remaining formalization is:

1. a finite gluing argument for the twenty local extensions, using C1's exact root classification;
2. use finite-sum linearity to combine the individual kernel integrals, then apply the existing
   Cauchy formula to the globally corrected analytic function and identify its Taylor coefficient.

Until these are proved in Lean, the formula above is a verified normalization and proof reduction,
not a compiled contour theorem. Neither the numerical probe nor the external root boxes supply any
of the analytic extension steps.
