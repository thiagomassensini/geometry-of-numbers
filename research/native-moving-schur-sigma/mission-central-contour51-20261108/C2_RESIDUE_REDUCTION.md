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

`SigmaContour51FiniteContour.lean` now completes this proof in Lean. The generic theorem
`exists_contour51_corrected_log_derivative` takes an analytic function, its exact finite set of
simple zeros in the closed disk, their strict interiority, and nonvanishing at the origin. At a
listed zero it uses the local simple-zero cancellation to define the corrected function by the
analytic extension plus the other regular pole terms; away from the zeros it uses the response plus
the full finite principal-part sum. This finite gluing proves regularity on the closed disk and the
boundary relation needed by the Cauchy reduction. Each kernel
`(z-alpha)^(-1) * z^(-k)` has zero radius-51 circle integral for `k ≥ 1`, as proved by induction on
`k`.

The same theorem calculates the corrected Taylor coefficient directly: it is the response's
original Taylor coefficient minus `(1/2) * sum_alpha alpha^(-1-n)`. The specialization
`exists_completedNative_contour51_corrected_log_derivative` applies C1's exact root classification
to the existing `completedNativeCharacteristicContinuation`. Finally,
`completedNative_contour51_jet_residue_identity` identifies the original response coefficient with
`completedSigmaLogJet 0 n` through the Carry source bridge and pairs the signed roots, giving the
explicit identity

```text
normalized ∮ R(z) / z^(2*n+2)
  = completedSigmaLogJet 0 n - sum_{i : Fin 10} (ts i)^(-2*n-2).
```

Here one fixed `ts` is selected by C1 for all `n`; every `ts i` also retains its exact rational
B2 height interval. No factorization of the entire function or infinite zero sum is used. The relevant theorem reports
from `#print axioms` are `[propext, Classical.choice, Quot.sound]`; the module compiles with
warnings as errors and introduces no `sorryAx` or new axiom. The successful final source, OLean,
and log hashes are recorded in `VALIDATION.md`.

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

## Formalization status and boundary

The finite gluing, boundary identity, Cauchy reduction, original-source coefficient normalization,
and signed-root pairing are all compiled in Lean 4.32.0 with warnings as errors. C2's radius-51
contour identity is therefore closed for every natural `n`. The Arb circle certificate and the
remaining finite residual signs belong to later checkpoints; the C2 theorem does not establish
unconditional positivity of all central Hankel minors by itself. The numerical probe and external
root boxes are not used as analytic proof steps in C2.

## Arb lower-path identity proved in Lean

`SigmaContour51ArbContourBridge.lean` proves the exact path reduction from the original source.
Evenness of `F` gives oddness of `R=-F'/(2F)`; dividing by `z^(2n+1)` gives an even quotient
`Q_n(z)=R(z)/z^(2n+1)`. C1's zero-free radius-51 boundary makes the angular quotient continuous.
For every `n`, Lean proves

```text
(2πi)⁻¹ ∮_{|z|=51} R(z)/z^(2n+2) dz
  = ∫₀¹ Q_n(circleMap 0 51 (-πu)) du.
```

This accounts for orientation, the circle derivative factor `iz`, π-periodicity, and the change
`θ=-πu`. The proposition `contour51ArbLowerPathResidualIntervalBounds` states the exact interval
inclusions in these lower-path coordinates; a proved adapter converts them to the circle-integral
gate used by the residual and determinant theorems. Thus the path and normalization are no longer
open. The source differential identity is also proved: for `F(z) ≠ 0`, Lean establishes
`R(z)=-(i/2) xiLean'(s)/xiLean(s)`, where `xiLean := sigmaCompletedXiParameter` and
`s=operatorHeightParameter z`. Under `0<Re(s)`, `s≠1`, and nonzero zeta, Lean now expands this
exactly to

```text
R(z) = -(i/2) * (1/s + 1/(s-1) - log(pi)/2
                   + digamma(s/2)/2 + zeta'(s)/zeta(s)).
```

For the source-response theorem, zeta nonvanishing is derived from `F(z)≠0` and the exact
completed-zeta factorization. `contour51OriginalResponse_eq_arb_formula_lower_path` discharges the
geometric side conditions uniformly for every lower-path parameter using C1's zero-free boundary
and the radius 51. The remaining open bridge is to check the external Taylor/Cauchy ranges against
this formal evaluator and integrate them over the full rational arc partition.

## The three remainder notions

- The **material tail** is the exact omitted-index sum in the native finite-head identity for the
  original C2 source. It is tied to the material cutoff and does not equal a ten-zero residual.
- The **central ten-mode residual** is
  `e_n = completedSigmaLogJet 0 n - ∑ i (ts i)^(-2*n-2)`. The theorem above proves it equals
  the normalized radius-51 contour integral for the original completed response.
- The **C4 contour-integral bound** is the norm estimate for the normalized contour integral. From
  `sup_|z|=51 |R(z)|≤4/5`, it gives `|e_n|≤40*(1/2500)^(n+1)` using the proved C2 residue identity
  and rational radius conversion. This is not the material tail and supplies no sign.
- The **Arb Taylor/Cauchy remainder** bounds omitted terms in the local Taylor evaluations of zeta
  and zeta-prime on each rational arc. Summing those complete-arc enclosures gives an external
  interval for the lower-path integral, hence for `e_n` only through the proved path identity.
  This numerical-analysis remainder is not a source tail or a second residual.
- The **C5 displaced coefficient and determinant remainders** are another family and need an
  explicit `d=0` interval transport before they can say anything about these central `e_n`.

No sign for any of these remainders is inferred without a separate theorem.
