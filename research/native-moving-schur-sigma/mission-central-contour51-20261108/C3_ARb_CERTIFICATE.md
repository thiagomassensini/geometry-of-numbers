# C3 — Arb certificate for the radius-51 contour bound

## Result and proof boundary

The interval computation proves, with python-flint 0.8.0 Arb/Acb ball arithmetic,

`|R(z)| < 4/5` for every `|z| = 51`,

where `F` is the existing completed native characteristic and
`R(z) = -F'(z)/(2 F(z))`. This is a reproducible computer-assisted certificate;
it is **not** yet a Lean theorem. The exact program is
`certify_contour51_bound.py`, and every arc enclosure is retained in
`evidence/C3_ARb_ARCS.csv`.

## Function evaluated

The existing source bridge identifies `F(z)` with the classical completed zeta
`xi(s)` at `s = 1/2 + i z`. Thus, writing `L(s) = xi'(s)/xi(s)`,

```text
R(z) = -i L(s)/2,
L(s) = 1/s + 1/(s-1) - log(pi)/2
       + digamma(s/2)/2 + zeta'(s)/zeta(s).
```

The script bounds `L` on the lower semicircle `z = 51 exp(-pi i u)`,
`0 ≤ u ≤ 1`. Evenness of the original `F` gives `R(-z) = -R(z)`, so the
modulus bound on the lower semicircle covers the upper semicircle as well.
Zeros are not used to define `F`, `R`, or any central moment.

On the Lean side, `completedNativeCharacteristicContinuation` is defined from
Mathlib's entire regularized completed zeta. In
`SigmaContour51ArbContourBridge.lean`, the exact source response has been
identified with `-(i/2)` times the explicit zeta/Gamma/digamma expression used
by Arb, with `F(z)≠0`, `0<Re(s)`, and `s≠1` stated; zeta nonvanishing follows
from the source factorization. `contour51OriginalResponse_eq_arb_formula_lower_path`
discharges the geometric conditions throughout the lower semicircle. The
remaining certificate bridge is to transfer the complete-arc Arb enclosures
and their Taylor/Cauchy remainders to Lean, then verify the rational weighted
endpoint sums. The exact integration step is now a compiled generic Lean
theorem, `contour51_intervalIntegral_bounds_of_uniform_partition`: pointwise
bounds on each rational subinterval imply the corresponding integral bounds.
It does not prove the evaluator inclusions or sum comparisons. The C2 residue
identity itself is already a compiled theorem for the original continuation.

## Coverage and interval method

The rational intervals `[k/512, (k+1)/512]`, for `k = 0,...,511`, partition
`[0,1]`. Arb encloses `pi`, the angle `-pi*u`, its sine and cosine, and hence
the complete complex `s` arc for each interval. No mesh-point inference is
used.

For an arc enclosure `S`, the script takes its Arb midpoint `s0` and bounds
`delta = S - s0`. It uses the Taylor polynomial of `zeta(s0 + delta)` through
degree 32. The radius `r = 1/4` disk contains every such arc because the
largest certified `|delta|/r` is below `0.626`. A square of half-width `1/4`
contains that disk; Arb evaluates zeta on the whole square to obtain a rigorous
majorant `M`. The program also checks that the center is more than 1 away from
the pole at `s=1`, so zeta is analytic on every Taylor disk.

Cauchy's coefficient estimate `|c_j| ≤ M/r^j` bounds the omitted tails. With
`q = |delta|/r < 1` and Taylor degree `N=32`, the bounds used are

```text
|zeta remainder|      <= M q^(N+1)/(1-q)
|zeta' remainder|     <= (M/r) q^N ((N+1)-Nq)/(1-q)^2.
```

Those error disks are added to the Arb Taylor-polynomial enclosures. The
certificate then checks that each zeta range excludes zero before dividing to
form `zeta'/zeta`. The rational and digamma terms are evaluated directly on
the full arc ball. It also checks that the arc range avoids `s=0` and `s=1`,
and that `Re(s)>0`, which keeps `digamma(s/2)` away from its poles. Every final
`|L|` enclosure is checked strictly below `8/5`.

## Recorded run

Command:

```text
python research/native-moving-schur-sigma/mission-central-contour51-20261108/certify_contour51_bound.py --csv research/native-moving-schur-sigma/mission-central-contour51-20261108/evidence/C3_ARb_ARCS.csv
```

Environment: Python 3.12.12, python-flint 0.8.0, 160-bit Arb precision,
512 arcs, Taylor degree 32. The recorded outward bounds are:

| Quantity | Certified bound |
|---|---:|
| maximum `|xi'/xi|` | `< 1.492825` |
| maximum `|R|` | `< 0.746413` |
| minimum `|zeta|` lower bound over arcs | `> 0.942660` |
| maximum Taylor ratio `|delta|/r` | `< 0.625864` |

The exact Arb balls for every arc are in the CSV; the script asserts all 512
strict inequalities and fails if any arc is not covered, zeta may vanish, or
the final `4/5` target is missed. The C3 analytic estimate is therefore
established with a small proof assistant dependency boundary at Arb. Importing
or re-proving this certificate in Lean remains open.

## Six original-source residual intervals

The companion `certify_contour51_residuals.py` reuses the same interval Taylor
and Cauchy-tail evaluator with 4096 rational parameter arcs. It encloses the
range of `R(z)/z^(2*n+1)` on every complete arc and adds each real interval
times its exact rational width. Since `F` is even, `R` is odd; with
`z(u)=51 exp(-pi*i*u)`, the positively oriented normalized full-circle
integral of `R(z)/z^(2*n+2)` equals the resulting half-circle parameter
integral. The Lean C2 theorem identifies that full integral with the original
central residual `e_n`. This calculation integrates the original source
response directly; it does not subtract approximate zero powers.

The exact outward rational interval endpoints are in
`evidence/C3_ARb_RESIDUALS_4096.json`; the compact run output is in the adjacent
`.log`. Lean verifies that the following strict rational lower margins lie
below the recorded Arb lower endpoints, and that the simple upper bounds below
lie above the recorded endpoints:

| `n` | Arb interval lower endpoint (decimal display) | Lean checked `e_n` lower margin | Lean checked upper bound |
|---:|---:|---:|---:|
| 0 | `9.535852947110655e-3` | `9/1000` | `1/100` |
| 1 | `9.180296036279536e-7` | `9/10000000` | `1/1000000` |
| 2 | `1.874202910399414e-10` | `9/50000000000` | `1/4000000000` |
| 3 | `4.542210478952836e-14` | `1/25000000000000` | `1/10000000000000` |
| 4 | `1.205912260570632e-17` | `1/100000000000000000` | `1/50000000000000000` |
| 5 | `2.797326848058986e-21` | `1/500000000000000000000` | `1/100000000000000000000` |

These are rigorous external Arb enclosures and rational comparisons checked in
Lean, but their inclusion in the actual Lean contour integrals is still an
explicit hypothesis of `SigmaContour51ArbResidualGate.lean`. The half-circle
parameterization, oddness reduction, lower-path identity, and generic
uniform-partition integration step are already formalized. The remaining
bridge is the transfer from each complete-arc Arb range, including its
Taylor/Cauchy remainder, to the Lean evaluator, and verification of the
weighted rational endpoint sums. Accordingly,
the six signs are externally certified but not yet discharged in Lean. The
first-window determinant now has a conditional Lean gate from just the three
intervals `e_0,e_1,e_2`; its exact rational margin proves
`1/1000000000 < sigmaPadeD 0 0` under those interval inclusions. The product
and square bounds retain all five terms in the determinant difference.

The six-residual run also executes the `|R|<4/5` check on each of its 4096
arcs through `certify_arc`. The independent 512-arc C3 run remains the recorded
uniform circle certificate. Neither run has yet supplied a Lean proof of the
circle premise used by the all-window `C=40` tail.
