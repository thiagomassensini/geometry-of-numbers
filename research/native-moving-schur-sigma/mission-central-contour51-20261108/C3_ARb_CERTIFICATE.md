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
