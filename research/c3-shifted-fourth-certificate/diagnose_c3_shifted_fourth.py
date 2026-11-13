#!/usr/bin/env python3
"""Reproduce C3 M=80/128 diagnostics and exact-rational 4x4 gate preflight.

The multiprecision values select candidate centers and a fixed rational
Bézout direction.  They are not source inclusions.  The gate calculation
below is exact over Fraction after the candidate rational coefficient boxes
have been supplied; Lean must still prove that the original C3 source lies
inside those boxes.
"""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from itertools import product

from mpmath import mp
import sympy as sp


ORDER = 16
DOUBLE_STENCIL = (
    531440, -1062856, 531116, 534040, -1077806, 596896,
    303810, -420006, -965379, 3428360, -5731741, 6760781,
    -6229340, 4668859, -2896919, 1496820, -642876, 227631,
    -65455, 14924, -2599, 325, -26, 1,
)


def completed_multipliers(w):
    s = mp.mpf(1) / 2 + mp.j * w
    elementary = s * (s - 1) * mp.power(mp.pi, -s / 2) / (
        2 * (1 - mp.power(3, 1 - s))
    )
    return elementary, elementary * mp.gamma(s / 2)


def c3_head_jets(cutoff: int) -> list:
    """Factorial-normalized source jets of the literal C3/48 bracket head."""
    source_jets = [mp.mpc(1)] + [mp.mpc(0)] * ORDER

    def add_sample(address: int, weight):
        log_address = mp.log(address)
        term = mp.mpf(weight) * mp.exp(-log_address / 2)
        for r in range(ORDER + 1):
            source_jets[r] += term
            term *= -mp.j * log_address / (r + 1)

    for cell in range(cutoff):
        for offset, weight in enumerate((1, -2, 1)):
            add_sample(3 * cell + 2 + offset, weight)
    for offset, weight in enumerate(DOUBLE_STENCIL):
        add_sample(3 * cutoff + 2 + offset, mp.mpf(weight) / 729**2)
    return source_jets


def source_coefficients(cutoff: int) -> list:
    """Taylor coefficients from the literal bracket head and completion."""
    source_jets = c3_head_jets(cutoff)

    multiplier_jets = mp.taylor(lambda w: completed_multipliers(w)[1], 0, ORDER)
    coefficients = []
    for j in range(9):
        r = 2 * j
        value = mp.fsum(multiplier_jets[k] * source_jets[r - k] for k in range(r + 1))
        coefficients.append(mp.re(value))
    return coefficients


def moment_sequence(c: list) -> list:
    h = []
    for k in range(8):
        h.append((-(k + 1) * c[k + 1] - sum(c[k - j] * h[j] for j in range(k))) / c[0])
    return h


def odd_bezout_entry_numeric(c: list, i: int, j: int):
    return mp.fsum(
        (j - k + 1) * c[j - k + 1] * c[i + k + 1]
        - (i + k + 2) * c[j - k] * c[i + k + 2]
        for k in range(j + 1)
    )


def fixed_direction(c: list) -> list[F]:
    bmat = mp.matrix([[odd_bezout_entry_numeric(c, i, j) for j in range(4)] for i in range(4)])
    prefix = bmat[:3, :3]
    coupling = bmat[:3, 3]
    critical = -(prefix**-1 * coupling)
    denominator = 10**21
    return [F(int(mp.nint(critical[i] * denominator)), denominator) for i in range(3)]


def sympy_bezout_entry(c, i: int, j: int):
    return sp.Add(*(
        (j - k + 1) * c[j - k + 1] * c[i + k + 1]
        - (i + k + 2) * c[j - k] * c[i + k + 2]
        for k in range(j + 1)
    ))


def exact_cofactor_gate(centers: list[F], radii: list[F], direction: list[F]):
    c = sp.symbols("c0:9")
    u = [sp.Rational(x.numerator, x.denominator) for x in direction]
    block = sp.Matrix([[sympy_bezout_entry(c, i, j) for j in range(4)] for i in range(4)])
    if not all(sp.expand(block[i, j] - block[j, i]) == 0 for i in range(4) for j in range(4)):
        raise AssertionError("the odd source Bézout block failed symmetry")
    a = block[:3, :3]
    b = block[:3, 3]
    d = block[3, 3]
    det_a = a.det(method="domain-ge")
    residual = a * sp.Matrix(u) + b
    energy = (sp.Matrix(u).T * a * sp.Matrix(u))[0] + 2 * (sp.Matrix(u).T * b)[0] + d
    cofactor_form = sp.expand(det_a * energy - (residual.T * a.adjugate() * residual)[0])
    det_block = sp.expand(block.det(method="domain-ge"))
    if sp.expand(cofactor_form - det_block) != 0:
        raise AssertionError("bordered cofactor identity disagrees with determinant")

    x = sp.symbols("x0:9")
    subs = {
        c[i]: sp.Rational(centers[i].numerator, centers[i].denominator) + x[i]
        for i in range(9)
    }
    shifted = sp.Poly(sp.expand(cofactor_form.subs(subs)), *x, domain=sp.QQ)
    det_a_center_expr = sp.cancel(det_a.subs({c[i]: sp.Rational(centers[i].numerator, centers[i].denominator)
        for i in range(9)}))
    constant = F(int(shifted.coeff_monomial((0,) * 9).p), int(shifted.coeff_monomial((0,) * 9).q))
    variation = F(0)
    for exponents, coeff in shifted.terms():
        if not any(exponents):
            continue
        q = F(int(coeff.p), int(coeff.q))
        term_radius = abs(q)
        for radius, exponent in zip(radii, exponents):
            if exponent:
                term_radius *= radius**exponent
        variation += term_radius
    det_a_center = F(int(det_a_center_expr.p), int(det_a_center_expr.q))
    return constant, variation, constant - variation, len(shifted.terms()), det_a_center


def rational_center(value) -> F:
    den = 10**50
    return F(int(mp.nint(value * den)), den)


def decimal_fraction(q: F, digits: int = 38) -> str:
    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--digits", type=int, default=125)
    parser.add_argument("--radius-exponents", nargs=9, type=int,
        default=[23, 23, 23, 23, 23, 23, 23, 23, 24],
        help="box radius for c_j is 10^(-exponent), j=0,...,8")
    args = parser.parse_args()
    mp.dps = args.digits

    by_cutoff = {m: source_coefficients(m) for m in (80, 128)}
    c = by_cutoff[80]
    h = moment_sequence(c)
    hankel = mp.matrix([[h[1 + i + j] for j in range(4)] for i in range(4)])
    p_h = hankel[3, 3] - (hankel[:3, 3].T * (hankel[:3, :3] ** -1) * hankel[:3, 3])[0]
    direction = fixed_direction(c)
    centers = [rational_center(x) for x in c]
    radii = [F(1, 10**e) for e in args.radius_exponents]

    print("C3 original bracket/completion diagnostics (diagnostic values only)")
    print("cutoff=80; stencil=C3Boundary48Stencil; completion unchanged")
    for j, value in enumerate(c):
        print(f"c{j} ~= {mp.nstr(value, 48)}")
    print(f"p_H,1,3 ~= {mp.nstr(p_h, 35)}")
    print(f"c0^2*p_H,1,3 ~= {mp.nstr(c[0]**2*p_h, 35)}")
    print("fixed rational Bézout prefix direction:")
    for j, value in enumerate(direction):
        print(f"  u{j} = {value.numerator}/{value.denominator} ({decimal_fraction(value)})")

    print("candidate exact-rational coefficient boxes:")
    for j, (center, radius) in enumerate(zip(centers, radii)):
        print(f"  c{j}: center={center.numerator}/{center.denominator}; radius={radius.numerator}/{radius.denominator}")
    constant, variation, lower, terms, det_a = exact_cofactor_gate(centers, radii, direction)
    print(f"fixed-direction polynomial terms: {terms}")
    print(f"det(A) at center ~= {decimal_fraction(det_a, 45)}")
    print(f"gate center = {decimal_fraction(constant, 50)}")
    print(f"exact variation bound = {decimal_fraction(variation, 50)}")
    print(f"exact gate lower bound = {decimal_fraction(lower, 50)}")
    print("gate status:", "PASS" if lower > 0 else "FAIL")

    tail16 = F(96 * 26 * 25 * 24 * 23 * 22 * 21 * 20 * 19 * 18 * 17 * 16 * 15 * 14 * 13 * 12 * 11 * 10 * 9 * 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1 * 4**16,
        729**2 * 239**25)
    print(f"M=80 original completed C3/48 tail bound at jet16 = {decimal_fraction(tail16, 38)}")
    head_jets = c3_head_jets(80)
    elementary_jets = mp.taylor(lambda w: completed_multipliers(w)[0], 0, ORDER)
    left_jets = [mp.fsum(elementary_jets[k] * head_jets[r-k]
        for k in range(r+1)) for r in range(ORDER+1)]
    print("weighted Gamma substitution ledger from the left-head jets:")
    for j in range(7, 9):
        r = 2 * j
        gamma_error = mp.fsum(abs(left_jets[k]) * 2 * mp.mpf(4)**(r-k) / mp.mpf(10)**34
            for k in range(r+1))
        tail_error = mp.mpf(tail16.numerator) / tail16.denominator / mp.mpf(4)**16 * mp.mpf(4)**r
        print(f"  c{j}: Gamma <= {mp.nstr(gamma_error, 18)}; tail <= {mp.nstr(tail_error, 18)}")
    print("source inclusion remains to be proved in Lean; this script does not certify it")


if __name__ == "__main__":
    main()
