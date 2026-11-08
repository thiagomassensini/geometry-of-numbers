# C2 central 2×2 — finite-contour route at radius 51 (research checkpoint)

**Date:** 2026-11-08. **State:** mathematical reduction + reproducible *non-certified* numerical probe + **exact** rational tests. **NOT a Lean proof** of unconditional central positivity. Separate branch from `main@ebd6c57`; does not change B1 PR #304, B2, or C5.

## Provenance: original source, not a spectral definition

The original C2 second-difference source passes through Genuine, native `N`, and the completion `F=A N`. Its log response is `R(z)=-F'(z)/(2F(z))`; the central jets are the Taylor coefficients `R(z)=sum_{n≥0} H_n z^(2n+1)`. In Lean, the path is `canonicalC2Geometry_finiteHead_add_exactTail_eq_factor_mul_nativeScalar` (Carry), `completedNativeCharacteristicContinuation_eq_native`, `sigma_log_jet_center_eq_canonical`, and `sigmaPadeD`. Here `F` means **the existing completed characteristic's entire continuation**, not a new function defined by zeros.

The exact C2 finite-material-head/omitted-material-tail identity is established on its native domain. It is **not** a global contour bound and its cutoff error is **not** automatically the ten-mode residual below. We use the established equal-germ bridge to the entire continuation.

## New conditional finite-contour identity (needs Lean formalization)

Write `F(z)=completedNativeCharacteristicContinuation(z)` and `R(z)=-F'(z)/(2F(z))`. Assume the existing certified finite-height results are assembled so that the **only** zeros in `|z|<51` are ten distinct, simple positive real ordinates `γ_1,...,γ_10` and their negative partners, and no zeros lie on `|z|=51`. The 52-height certificate is already present in `RHHeight/Main.lean`: `ncount_three_fiftytwo : Zeta23.Ncount 3 52=10`, `rh_up_to_height_fiftytwo`, and `low_height`; it is not yet packaged in a central contour theorem.

Define `a_j=γ_j^(-2)`, `P_n=sum_{j=1}^{10} a_j^(n+1)`, and `e_n := H_n-P_n` (comparison only). The residue theorem gives, **for every n≥0**,

```math
e_n = (1/(2πi)) ∮_{|z|=51} [R(z) / z^(2n+2)] dz.
```

At `z=0`, the residue is `H_n`. Every simple zero `z=±γ_j` gives `Res R=-1/2`; their combined contribution to the integrand is `-γ_j^(-2n-2)`. This is a finite residue identity: **no global Hadamard factorization, infinite zero sum, or Lehman tail is needed**.

The circle estimate

```math
forall |z|=51, |R(z)| ≤ 4/5
```

would imply for all n,

```math
|e_n| ≤ (4/5)/51^(2n+1) ≤ 40*(1/2500)^(n+1).
```

A convenient denominator-free equivalent certificate, given `F(z) ≠ 0` on the circle, is `25*|F'(z)|² ≤ 64*|F(z)|²`. The uniform `|R|≤4/5` bound has now been certified on the full circle by the reproducible Arb interval computation in `C3_ARb_CERTIFICATE.md`; the interval certificate is not yet imported or re-proved in Lean.

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

Consequently, assuming `e_n≥0` for `0≤n≤5`, these four strict margins imply `D_s(H)>0` for `0≤s<4`. For `s≥4`, `|e_n|≤40*eta^(n+1)` implies the existing B1 `|e_n|≤60*eta^(n+1)`; B1's already compiled `hankel2_pos_large_of_ten_boxes_and_global_tail` applies. Therefore:

> **Conditional target:** ten certified scales + the finite-contour identity + uniform circle bound `|R|≤4/5` + six finite signs `e_0,...,e_5≥0` imply `forall s, sigmaPadeD 0 s > 0`. The refined Lehman `T_1,...,T_4` obligations can be **replaced** by this stronger global estimate and a new rational gate. This does not discharge B1's current `htail` premise verbatim.

## Independent numerical probe — NOT A CERTIFICATE

`reproduce.py` evaluates `-F'/(2F)` using the regularized xi formula and the functional equation to stay on the stable half-plane. It uses 2048 equally spaced points on `|z|=51` (65 decimal digits), plus a 256-point Taylor/Cauchy probe at radius 8. The ten heights from `mp.zetazero` are used **only to subtract P**, not to define H or F.

- Sample maximum on `|z|=51`: **0.6345202216511754**, below the proposed 0.8.
- Sample mean modulus: **0.5695801987243165**.
- Residuals `e_0..e_5` numerically: `0.00956074303923091`, `9.34518811591709e-7`, `1.97785053903660e-10`, `5.13925976411857e-14`, `1.46980503972282e-17`, `4.44431065896308e-21`.

**Neither a finite mesh nor floating-point Cauchy coefficients prove a uniform bound or positivity.** All six signs and the circle estimate require rigorous interval/Lean certification. Independent implementation of `F` and `F'` must be checked against the native normalization; the numerical probe additionally cross-checked at sample points against direct differentiation of xi.

## Minimal next checkpoints

1. **C0 / isolation and source audit:** complete; the independent contour branch and provenance are recorded in this mission directory.
2. **C1 / disk roots:** reuse B2's ten height witnesses and the 52-height weighted count to prove exactly ten simple pairs in `|z|<51`, no boundary zeros, and center-germ equality with the original C2 jets. Do not conflate distinct-zero count and multiplicity.
3. **C2 / finite residues:** formalize the finite contour identity above in Lean for every `n`, with local analytic cancellation and finite gluing. No global factorization is needed.
4. **C3 / uniform interval bound:** complete as a computer-assisted certificate. `certify_contour51_bound.py` encloses all 512 rational parameter arcs with Arb Taylor bounds and proves `|R|<4/5`; the certificate is not yet a Lean theorem.
5. **C4 / all-order tail:** use the finite contour identity, the C3 bound, and the exact radius conversion to prove `|e_n|≤40*(1/2500)^(n+1)` in Lean.
6. **C5 / six original-source signs:** certify `H_n-P_n≥0`, `n=0,...,5`, from the *original* characteristic/germ using interval jets and the actual ten rational root boxes. The material-cell tail alone does not imply these signs.
7. **C6 / rational gate:** prove the four `M40_s>0` margins in Lean, combine with B1's existing `s≥4` proof, and audit transitive axioms with warnings as errors.

**Scope:** consecutive central 2×2 Hankel minors only. No all-dimension Hankel PSD claim, no global zero location claim. No `sorry`, `admit`, mathematical axioms, or substitution of a zero-defined source.

## Source pointers

- [Carry exact C2 native bridge](https://github.com/thiagomassensini/carry-self-adjoint-operator/blob/main/CarrySelfAdjointOperator/C2GeometryNativeSourceBridge.lean)
- [Entire native continuation and equality of germs](https://github.com/thiagomassensini/geometry-of-numbers/blob/main/research/native-moving-schur-sigma/SigmaNativeContinuation.lean)
- [Height-52 count, simplicity](https://github.com/thiagomassensini/geometry-of-numbers/blob/main/research/native-moving-schur-sigma/height50-certified/hunts/rh_height_lean/lean/RHHeight/Main.lean)
- [B1 strict rational gates and global large-window theorem](https://github.com/thiagomassensini/geometry-of-numbers/blob/agent/c2-central-hankel2-allorder-20261107/research/native-moving-schur-sigma/SigmaCentralTenModeRationalGate.lean)
