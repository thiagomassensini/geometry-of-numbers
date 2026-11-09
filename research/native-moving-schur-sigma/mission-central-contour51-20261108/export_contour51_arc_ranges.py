#!/usr/bin/env python3
"""Export outward-rational complete-arc ranges for the first six C2 residuals.

This preserves the per-arc interval inputs used by the external Arb calculation so
the Lean certificate can separately verify the exact rational weighted sums. It
does not turn Arb evaluation into a Lean theorem.
"""

import argparse
import json
from fractions import Fraction
from pathlib import Path

from flint import acb, arb, ctx, fmpq

import certify_contour51_bound as c3
from certify_contour51_residuals import arb_outer_fraction


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--arcs", type=int, default=4096)
    parser.add_argument("--precision", type=int, default=160)
    parser.add_argument("--max-n", type=int, default=5)
    parser.add_argument(
        "--json",
        type=Path,
        default=Path("C3_ARb_RESIDUAL_ARCS_4096.json"),
    )
    args = parser.parse_args()
    if args.arcs <= 0:
        raise ValueError("arc count must be positive")
    if args.max_n < 0 or args.max_n > 5:
        raise ValueError("max-n must be between 0 and 5")
    if c3.flint.__version__ != "0.8.0":
        raise RuntimeError(
            f"expected python-flint 0.8.0, found {c3.flint.__version__}"
        )

    ctx.prec = args.precision
    ctx.cap = c3.TAYLOR_ORDER + 1
    pi = arb.pi()
    log_pi = pi.log()
    width = Fraction(1, args.arcs)
    order_count = args.max_n + 1
    weighted_lower = [Fraction(0) for _ in range(order_count)]
    weighted_upper = [Fraction(0) for _ in range(order_count)]
    rows = []

    for index in range(args.arcs):
        arc = c3.certify_arc(index, pi, log_pi, arc_count=args.arcs)
        response = -acb(0, 1) * arc["log_derivative"] / 2
        residual_ranges = []
        for n in range(order_count):
            integrand = response / arc["z_arc"] ** (2 * n + 1)
            lower = arb_outer_fraction(integrand.real, lower=True)
            upper = arb_outer_fraction(integrand.real, lower=False)
            if lower > upper:
                raise ArithmeticError(f"arc {index}, n={n}: invalid interval")
            weighted_lower[n] += width * lower
            weighted_upper[n] += width * upper
            residual_ranges.append({"lower": str(lower), "upper": str(upper)})
        rows.append({"index": index, "residual_ranges": residual_ranges})

    output = {
        "certificate": "Outward rational per-arc ranges for the original C2 response integrals",
        "python_flint": c3.flint.__version__,
        "precision_bits": args.precision,
        "arcs": args.arcs,
        "max_n": args.max_n,
        "taylor_order": c3.TAYLOR_ORDER,
        "parameterization": "R(51*exp(-pi*i*u))/(51*exp(-pi*i*u))^(2*n+1), u in [k/N,(k+1)/N]",
        "arc_width": str(width),
        "weighted_sums": [
            {
                "n": n,
                "lower": str(weighted_lower[n]),
                "upper": str(weighted_upper[n]),
            }
            for n in range(order_count)
        ],
        "intervals": rows,
    }
    args.json.parent.mkdir(parents=True, exist_ok=True)
    args.json.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")

    for n in range(order_count):
        print(
            f"n={n}: weighted enclosure [{float(weighted_lower[n]):.15e}, "
            f"{float(weighted_upper[n]):.15e}]"
        )
    print(f"per-arc rational ranges: {args.json}")


if __name__ == "__main__":
    main()
