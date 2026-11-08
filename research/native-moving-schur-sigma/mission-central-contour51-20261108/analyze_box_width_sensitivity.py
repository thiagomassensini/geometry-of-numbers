#!/usr/bin/env python3
"""Exact rational sensitivity analysis for the current ten-height boxes.

The power-sum box widths and each ordinate's contribution are computed with
fractions.  The comparison to the recorded mpmath residual probes is only a
prioritization diagnostic; it is not an interval enclosure or sign proof.
"""

from decimal import Decimal, getcontext
from fractions import Fraction


getcontext().prec = 40

LOWER = [Fraction(x, 100) for x in
         (1413, 2102, 2501, 3042, 3293, 3758, 4091, 4332, 4800, 4977)]
UPPER = [x + Fraction(1, 100) for x in LOWER]
RESIDUAL_PROBES = [
    Decimal("0.00956074303923091"),
    Decimal("9.34518811591709e-7"),
    Decimal("1.97785053903660e-10"),
    Decimal("5.13925976411857e-14"),
    Decimal("1.46980503972282e-17"),
    Decimal("4.44431065896308e-21"),
]
LEAN_WIDTH_BUDGETS = [
    Fraction(14, 1_000_000),
    Fraction(9, 100_000_000),
    Fraction(6, 10_000_000_000),
    Fraction(4, 1_000_000_000_000),
    Fraction(3, 100_000_000_000_000),
    Fraction(2, 10_000_000_000_000_000),
]


def as_decimal(q):
    return Decimal(q.numerator) / Decimal(q.denominator)


def contribution(index, n):
    exponent = 2 * (n + 1)
    return Fraction(1, LOWER[index] ** exponent) - Fraction(1, UPPER[index] ** exponent)


def main():
    print("Current B2 ten-mode interval widths (exact Fraction arithmetic)")
    print("Residual values below are old mpmath probes, not certified margins.")
    for n, probe in enumerate(RESIDUAL_PROBES):
        terms = [contribution(i, n) for i in range(10)]
        width = sum(terms, Fraction(0))
        assert width < LEAN_WIDTH_BUDGETS[n]
        ratios = [as_decimal(term) / probe for term in terms]
        remaining = Decimal(0)
        refine_count = 10
        for count in range(10, -1, -1):
            remaining = sum(ratios[count:], Decimal(0))
            if remaining < Decimal("0.5"):
                refine_count = count
        print(
            f"n={n}: exact width={width.numerator}/{width.denominator}; "
            f"decimal={as_decimal(width):.16E}; "
            f"width/probe={as_decimal(width) / probe:.6E}; "
            f"leading intervals to refine for remaining < 0.5*probe={refine_count}"
        )
        print("  per-index contribution/probe=" + ", ".join(
            f"{i}:{ratio:.4E}" for i, ratio in enumerate(ratios)
        ))
    print("All width-budget assertions passed exactly.")
    print("The probe comparison only prioritizes possible interval refinement.")


if __name__ == "__main__":
    main()
