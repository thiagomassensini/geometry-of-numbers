#!/usr/bin/env python3
"""Arb range-integral enclosures for the first six contour residuals.

The C2 Lean residue theorem identifies each residual directly with a normalized
contour integral. Parameterizing the circle reduces it to an integral over a
half-circle of R(z)/z^(2n+1); the integrand is invariant under z -> -z. On each
rational parameter arc, the C3 Taylor/Cauchy calculation encloses the complete
range of the integrand. Summing those ranges times exact arc widths encloses
the residual.

This is a rigorous external Arb certificate, not yet a Lean proof. The exact
ten-mode subtraction is already part of the proved C2 residue identity, so this
calculation does not numerically subtract approximate zero sums.
"""

import argparse
import json
from fractions import Fraction
from pathlib import Path

import certify_contour51_bound as c3
from flint import acb, arb, ctx, fmpq


RATIONAL_LOWER_MARGINS = [
    Fraction(9, 1000),
    Fraction(9, 10_000_000),
    Fraction(18, 100_000_000_000),
    Fraction(4, 100_000_000_000_000),
    Fraction(1, 100_000_000_000_000_000),
    Fraction(2, 1_000_000_000_000_000_000_000),
]


def arb_outer_fraction(x, lower):
    """Convert an Arb enclosure endpoint to an exact outward rational bound."""
    endpoint_ball = x.lower() if lower else x.upper()
    mid, radius, exp10 = endpoint_ball.mid_rad_10exp()
    exponent = int(exp10)
    scale = Fraction(10**exponent, 1) if exponent >= 0 else Fraction(1, 10**(-exponent))
    mid_q = Fraction(int(mid)) * scale
    radius_q = Fraction(int(radius)) * scale
    return mid_q - radius_q if lower else mid_q + radius_q


def contour_integral_boxes(arc_count, pi, log_pi):
    """Enclose Re ∫ R(z(u))/z(u)^(2n+1) du = e_n, for n=0,...,5."""
    totals = [arb(0) for _ in range(6)]
    step = arb(fmpq(1, arc_count))
    for index in range(arc_count):
        arc = c3.certify_arc(index, pi, log_pi, arc_count=arc_count)
        response = -acb(0, 1) * arc["log_derivative"] / 2
        for n in range(6):
            integrand = response / arc["z_arc"] ** (2 * n + 1)
            totals[n] += integrand.real * step
    return totals


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--arcs", type=int, default=4096)
    parser.add_argument("--precision", type=int, default=160)
    parser.add_argument(
        "--json", type=Path,
        default=Path("C3_ARb_RESIDUALS.json"),
        help="write exact rational bounds for the six residuals",
    )
    args = parser.parse_args()
    if args.arcs <= 0:
        raise ValueError("arc count must be positive")
    if c3.flint.__version__ != "0.8.0":
        raise RuntimeError(f"expected python-flint 0.8.0, found {c3.flint.__version__}")

    ctx.prec = args.precision
    ctx.cap = c3.TAYLOR_ORDER + 1
    pi = arb.pi()
    log_pi = pi.log()

    rows = []
    residual_boxes = contour_integral_boxes(args.arcs, pi, log_pi)
    for n in range(6):
        residual_lo = arb_outer_fraction(residual_boxes[n], lower=True)
        residual_hi = arb_outer_fraction(residual_boxes[n], lower=False)
        margin = RATIONAL_LOWER_MARGINS[n]
        if margin >= residual_lo:
            raise ArithmeticError(f"n={n}: rational margin exceeds Arb lower endpoint")
        row = {
            "n": n,
            "residual_lower": str(residual_lo),
            "residual_upper": str(residual_hi),
            "strict_rational_lower_margin": str(margin),
            "residual_lower_positive": residual_lo > 0,
        }
        rows.append(row)
        print(
            f"n={n}: e_n in approximately "
            f"[{float(residual_lo):.15e}, {float(residual_hi):.15e}]; "
            f"strict_rational_margin={margin}; certified_positive={residual_lo > 0} "
            "(exact rational endpoints are in the JSON)"
        )

    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps({
        "certificate": "Arb interval range integration of the original C2 contour response",
        "python_flint": c3.flint.__version__,
        "precision_bits": args.precision,
        "arcs": args.arcs,
        "taylor_order": c3.TAYLOR_ORDER,
        "parameterization": "Cauchy integral reduces to integral of R(51*exp(-pi*i*u))/(51*exp(-pi*i*u))^(2n+1), u in [0,1]",
        "identity": "e_n equals the full normalized Cauchy integral by completedNative_contour51_jet_residue_identity; the half-circle reduction uses R(-z)=-R(z)",
        "residuals": rows,
    }, indent=2) + "\n", encoding="utf-8")
    if not all(row["residual_lower_positive"] for row in rows):
        raise ArithmeticError("at least one residual interval does not certify positivity")
    print(f"exact rational certificate data: {args.json}")


if __name__ == "__main__":
    main()
