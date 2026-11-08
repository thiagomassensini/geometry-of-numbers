# C2 central 2×2 — finite-contour route at radius 51 (research checkpoint)

**Date:** 2026-11-08. **State:** C1 root classification and the C2 radius-51 contour identity are compiled in Lean; Arb externally certifies both the radius bound and rational intervals for the first six original-source residuals; C4/C6 and interval-conditional first/all-window gates compile in Lean. The Arb-to-Lean inclusion proofs remain open, so no unconditional positivity is claimed. This is a separate stacked branch and does not alter B1 PR #304, B2, or the parallel C5 worktree.

## Provenance: original source, not a spectral definition

The original C2 second-difference source passes through Genuine, native `N`, and the completion `F=A N`. Its log response is `R(z)=-F'(z)/(2F(z))`; the central jets are the Taylor coefficients `R(z)=sum_{n≥0} H_n z^(2n+1)`. In Lean, the path is `canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar` (Carry), `completedNativeCharacteristicContinuation_eq_native`, `sigma_log_jet_center_eq_canonical`, and `sigmaPadeD`. Here `F` means **the existing completed characteristic's entire continuation**, not a new function defined by zeros.

The exact C2 finite-material-head/omitted-material-tail identity is established on its native domain. It is **not** a global contour bound and its cutoff error is **not** automatically the ten-mode residual below. We use the established equal-germ bridge to the entire continuation.

## Finite-contour identity (proved in Lean)

Write `F(z)=completedNativeCharacteristicContinuation(z)` and `R(z)=-F'(z)/(2F(z))`. `SigmaContour51DiskBridge.lean` assembles the certified finite-height results so the only zeros in `|z|≤51` are ten distinct, simple positive real ordinates `γ_1,...,γ_10` and their negative partners, with no boundary zeros. It uses `ncount_three_fiftytwo : Zeta23.Ncount 3 52=10`, `rh_up_to_height_fiftytwo`, and `low_height`.

Define `a_j=γ_j^(-2)`, `P_n=sum_{j=1}^{10} a_j^(n+1)`, and `e_n := H_n-P_n` (comparison only). The compiled theorem `completedNative_contour51_jet_residue_identity` gives, **for every n≥0**,

```math
e_n = (1/(2πi)) ∮_{|z|=51} [R(z) / z^(2n+2)] dz.
```

At `z=0`, the normalized Cauchy coefficient is `H_n`. Each simple zero `z=±γ_j` contributes `-1/(2*(±γ_j)^(2n+2))`; each pair contributes `-γ_j^(-2n-2)`. The Lean proof constructs and glues the finite analytic correction across the twenty simple zeros, integrates the pole kernels to zero, applies Cauchy's formula, and identifies the source coefficient. This finite identity uses **no global Hadamard factorization, infinite zero sum, or Lehman tail**. Full details are in `C2_RESIDUE_REDUCTION.md`.

The circle estimate

```math
forall |z|=51, |R(z)| ≤ 4/5
```

would imply for all n,

```math
|e_n| ≤ (4/5)/51^(2n+1) ≤ 40*(1/2500)^(n+1).
```

A convenient denominator-free equivalent certificate, given `F(z) ≠ 0` on the circle, is `25*|F'(z)|² ≤ 64*|F(z)|²`. The uniform `|R|≤4/5` bound has been certified on the full circle by the reproducible Arb interval computation in `C3_ARb_CERTIFICATE.md`; the interval certificate is not yet imported or re-proved in Lean.

## New C=40 rational gate: exact arithmetic checked

The boxes are exactly those in B1's `SigmaCentralTenModeRationalGate.lean`: ordinate lower/upper endpoints `(14.13,14.14),...,(49.77,49.78)`, and `a_j ∈ [1/upper_j²,1/lower_j²]`. Let `P_lo(s)`, `P_hi(s)` be the two extreme power sums; let `eta=1/2500`. Define

```math
M40_s = P_lo(s)*P_lo(s+2) - (P_hi(s+1) + 40*eta^(s+2))².
```

The accompanying script asserts **with Python Fraction rational arithmetic**:

| s | exact-rational positive margin (decimal display only) |
|---|---:|
| 0 | 1.233805751396619e-10 |
| 1 | 2.370461448625535e-15 |
| 2 | 1.677704301041960e-20 |
| 3 | 4.956177598481227e-26 |

The determinant transport retains every term in the exact expansion, already formalized by
`hankel2_add_error_expansion`:

```text
D_s(H) - D_s(P) =
    P_s*e_(s+2) + e_s*P_(s+2) - 2*P_(s+1)*e_(s+1)
  + e_s*e_(s+2) - e_(s+1)^2.
```

Here `P` is the finite ten-mode comparison, and `e_n=H_n-P_n` is the contour residual. The exact
C2 omitted-material tail and the Cauchy/contour estimate are separate quantities; the contour
residual equals the normalized contour integral only by the proved C2 residue identity. No
percentage-of-cancellation estimate is used in the positivity gates.

Consequently, assuming `e_n≥0` for `0≤n≤5`, these four strict margins imply `D_s(H)>0` for `0≤s<4`. For `s≥4`, `|e_n|≤40*eta^(n+1)` implies the existing B1 `|e_n|≤60*eta^(n+1)`; B1's already compiled `hankel2_pos_large_of_ten_boxes_and_global_tail` applies. Therefore:

> **Conditional target:** the compiled `completedNative_sigmaPadeD_pos_of_contour51_bound` theorem proves that the original-source circle bound `‖R‖≤4/5` and six finite signs `e_0,...,e_5≥0` imply `forall s, sigmaPadeD 0 s > 0`. The C2 identity fixes the ten heights for all orders, and the C2→C4→C6 source bridge derives the scale boxes and decomposition. Arb now supplies exact rational intervals for the six signs, but neither those enclosures nor the circle bound have been transferred to Lean, so the hypotheses remain open. This does not discharge B1's current `htail` premise verbatim.

The companion Arb computation integrates the original response on 4096 complete parameter arcs and encloses all six normalized contour integrals. `SigmaContour51ArbResidualGate.lean` records the exact rational endpoints and verifies strict lower and upper margins. Its proposition `contour51ArbResidualIntervalBounds` explicitly represents the six-interval transfer; `contour51ArbFirstThreeResidualIntervalBounds` is the minimal transfer for `n=0,1,2`. The direct `completedNative_sigmaPadeD_zero_pos_of_contour51_arb_intervals` gate takes only the latter and proves the absolute determinant bound `1/1000000000 < sigmaPadeD 0 0`; this route does not need the global C3 tail bound.

## Exact width budgets and C5 center transport

`SigmaContour51BoxSensitivity.lean` proves the current B2 ten-mode interval widths are strictly below these rational budgets:

| `n` | Rational width budget | Approximate exact width from Fraction arithmetic | Width / old non-certified `e_n` probe |
|---:|---:|---:|---:|
| 0 | `14/10^6` | `1.3038935355470468e-5` | `1.36e-3` |
| 1 | `9/10^8` | `8.8707651982351861e-8` | `9.49e-2` |
| 2 | `6/10^10` | `5.8021702152449330e-10` | `2.93` |
| 3 | `4/10^12` | `3.6785120434605851e-12` | `71.6` |
| 4 | `3/10^14` | `2.2551276469308842e-14` | `1.53e3` |
| 5 | `2/10^16` | `1.3430971414644236e-16` | `3.02e4` |

The last column compares exact rational box widths with floating-point probes only as a historical refinement diagnostic; it does not certify a residual margin. Under that provisional comparison, the first one, three, four, and five height intervals dominate the uncertainty for `n=2,3,4,5`, respectively. The new Arb contour intervals evaluate the original response and do not use approximate zero ordinates or box centers, so their signs do not require narrowing the ten height boxes. Keep the formal B2 boxes because they identify the finite modes in the C2 residue identity.

The formal C5 center map is now explicit: `displacedProductC 0 z` is the square of `completedNativeOperatorCharacteristic z`; on the genuine native strip, the compiled theorem `c5CentralDisplacedProduct_eq_continuation_square` identifies it with the square of `completedNativeCharacteristicContinuation z`, which is the function used by the radius-51 contour proof. The strip condition remains explicit; this is not a claimed global equality outside the proved native strip. The generic displaced-source recurrence at `d=0` gives coefficient sequence `2*completedSigmaLogJet 0 n`; and `e_n = completedSigmaDisplacedMoment 0 n / 2 - P_n`. The audit `SigmaSourceBezoutAudit.lean` compiles with standard axioms and retains the original density/product and sigma jets. The C5 boxes at `d=99/2000` and `d=1/10` still need quantitative transport in `d` or direct center evaluation. No C5 Bernoulli or zeta/Gamma node certification was repeated.

## Independent numerical probe — NOT A CERTIFICATE

`reproduce.py` evaluates `-F'/(2F)` using the regularized xi formula and the functional equation to stay on the stable half-plane. It uses 2048 equally spaced points on `|z|=51` (65 decimal digits), plus a 256-point Taylor/Cauchy probe at radius 8. The ten heights from `mp.zetazero` are used **only to subtract P**, not to define H or F.

- Sample maximum on `|z|=51`: **0.6345202216511754**, below the proposed 0.8.
- Sample mean modulus: **0.5695801987243165**.
- Residuals `e_0..e_5` numerically: `0.00956074303923091`, `9.34518811591709e-7`, `1.97785053903660e-10`, `5.13925976411857e-14`, `1.46980503972282e-17`, `4.44431065896308e-21`.

**Neither a finite mesh nor floating-point Cauchy coefficients prove a uniform bound or positivity.** The Arb scripts now give rigorous external interval certificates for the uniform circle bound and all six residuals. Their analytic and interval calculations are not yet formalized in Lean; the earlier mpmath probe remains only a numerical cross-check.

## Minimal next checkpoints

1. **C0 / isolation and source audit:** complete; the independent contour branch and provenance are recorded in this mission directory.
2. **C1 / disk roots:** reuse B2's ten height witnesses and the 52-height weighted count to prove exactly ten simple pairs in `|z|<51`, no boundary zeros, and center-germ equality with the original C2 jets. Do not conflate distinct-zero count and multiplicity.
3. **C2 / finite residues:** complete. `SigmaContour51FiniteContour.lean` proves the source-normalized identity for every `n`; see `C2_RESIDUE_REDUCTION.md` and `VALIDATION.md`.
4. **C3 / uniform interval bound:** complete as a computer-assisted certificate. `certify_contour51_bound.py` encloses all 512 rational parameter arcs with Arb Taylor bounds and proves `|R|<4/5`; the certificate is not yet a Lean theorem.
5. **C4 / all-order tail:** the conditional Lean theorem deriving `|e_n|≤40*(1/2500)^(n+1)` from C2, the C3 circle bound, and exact radius conversion is complete. Discharging the circle-bound hypothesis in Lean remains open.
6. **C5 / six original-source signs:** the 4096-arc Arb run now gives rational lower and upper intervals for `H_n-P_n`, `n=0,...,5`, from the original contour response. Prove their inclusion in the formal Lean contour integrals; the material-cell tail alone does not imply these signs.
7. **C6 / rational gate:** complete. `SigmaContour51RationalGate.lean` proves the four exact `M40_s>0` margins and combines them with B1's `s≥4` proof; `SigmaContour51SourceTail.lean` specializes the conditional closure to the original completed characteristic. The Lean circle bound and six Arb interval transfers remain explicit for all windows. The first-window interval gate needs only the transfers for indices 0,1,2.

**Scope:** consecutive central 2×2 Hankel minors only. No all-dimension Hankel PSD claim, no global zero location claim. No `sorry`, `admit`, mathematical axioms, or substitution of a zero-defined source.

## Source pointers

- [Carry exact C2 native bridge](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/C2GeometryNativeSourceBridge.lean)
- [Entire native continuation and equality of germs](https://github.com/thiagomassensini/geometry-of-numbers/blob/main/research/native-moving-schur-sigma/SigmaNativeContinuation.lean)
- [Height-52 count, simplicity](https://github.com/thiagomassensini/geometry-of-numbers/blob/main/research/native-moving-schur-sigma/height50-certified/hunts/rh_height_lean/lean/RHHeight/Main.lean)
- [B1 strict rational gates and global large-window theorem](https://github.com/thiagomassensini/geometry-of-numbers/blob/agent/c2-central-hankel2-allorder-20261107/research/native-moving-schur-sigma/SigmaCentralTenModeRationalGate.lean)

## Lean path bridge update — 2026-11-08

`SigmaContour51ArbContourBridge.lean` now compiles the exact identity from the original completed
continuation to the lower semicircle parameter used in the external Arb residual integration:

```text
(2πi)⁻¹ ∮ R(z)/z^(2n+2) dz
  = ∫₀¹ (R(z(u))/z(u)^(2n+1)) du,
  z(u)=circleMap 0 51 (-πu).
```

Lean proves `R` odd from `F` even, proves the quotient even and π-periodic, accounts for circle
orientation and the `iz` derivative factor, and derives continuity from C1's zero-free circle. The
adapter from `contour51ArbLowerPathResidualIntervalBounds` to the prior C2 interval proposition is
also compiled. The source response is now connected to the explicit Arb evaluator:
`contour51OriginalResponse_eq_arb_formula` proves the zeta/Gamma/digamma expression under
`F(z)≠0`, `0<Re(s)`, and `s≠1`, deriving zeta nonvanishing from the exact source factorization.
`contour51OriginalResponse_eq_arb_formula_lower_path` discharges those conditions throughout the
lower path. The remaining C3/C5 bridge is to show the per-arc rational intervals enclose the
formal evaluator there, validate Taylor/Cauchy remainder ranges, and verify the rational weighted
endpoint sums. The exact integration step from pointwise arc bounds to their weighted integral
bounds is proved by `contour51_intervalIntegral_bounds_of_uniform_partition`; the certificate
inclusions and endpoint-sum comparisons are not Lean theorems yet.
For the first determinant, only `n=0,1,2` inclusions are required; the resulting strict absolute
margin is `1/1000000000`. All six strict residual lower margins are recorded in
`CHECKPOINTS.md`. The uniform `|R|≤4/5` Lean theorem is independently open for the all-window route.

This progress does not identify the C2 omitted-material tail, the ten-mode residual `e_n=H_n-P_n`,
and the Arb Taylor/Cauchy remainder. Only the proved residue identity and lower-path identity
relate `e_n` to the contour integral; the Taylor/Cauchy remainder only supports an external
interval enclosure until its transfer is formalized. The C5 displaced-box signs still need an
explicit interval transport to `d=0`; this branch reused no Bernoulli table or full zeta/Gamma node
certificate.
