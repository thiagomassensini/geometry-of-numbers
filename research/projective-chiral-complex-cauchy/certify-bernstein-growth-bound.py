#!/usr/bin/env python3
"""Certify the finite analytic inputs to BERNSTEIN_GROWTH_RATE.md."""

from flint import acb, acb_series, arb, ctx, fmpq


Q = fmpq(22, 175)
ZERO_FREE_HEIGHT = 14


def interval(lo, hi):
    return arb((lo + hi) / 2, (hi - lo) / 2)


def completed_zero_free_rectangle():
    # Reflection and conjugation extend this check to the full critical strip.
    boxes = [(fmpq(1, 2), fmpq(1), fmpq(0), fmpq(ZERO_FREE_HEIGHT), 0)]
    count = 0
    max_depth = 0
    lower_modulus = None
    while boxes:
        real_lo, real_hi, imag_lo, imag_hi, depth = boxes.pop()
        rectangle = acb(interval(real_lo, real_hi), interval(imag_lo, imag_hi))

        # Deflation subtracts 1/(s-1), so the regularization encloses (s-1) zeta(s)
        # also on rectangles containing the removable singularity at s=1.
        deflated = acb_series([rectangle]).zeta(deflate=True)[0]
        modulus = abs(1 + (rectangle - 1) * deflated)
        if modulus > 0:
            lower = modulus.lower()
            lower_modulus = lower if lower_modulus is None else min(lower_modulus, lower)
            count += 1
            max_depth = max(max_depth, depth)
            continue

        if depth == 30:
            raise ArithmeticError(f"Could not exclude zero on {rectangle}")
        if real_hi - real_lo >= imag_hi - imag_lo:
            mid = (real_lo + real_hi) / 2
            boxes.extend([
                (real_lo, mid, imag_lo, imag_hi, depth + 1),
                (mid, real_hi, imag_lo, imag_hi, depth + 1),
            ])
        else:
            mid = (imag_lo + imag_hi) / 2
            boxes.extend([
                (real_lo, real_hi, imag_lo, mid, depth + 1),
                (real_lo, real_hi, mid, imag_hi, depth + 1),
            ])

    print(f"Zero-free rectangle: {count} boxes, max depth {max_depth}")
    print(f"Global lower bound for |(s-1) zeta(s)|: {lower_modulus.str(15)}")


def verify_growth_constants():
    inverse_radius = fmpq(1, ZERO_FREE_HEIGHT**2)
    relative_radius = inverse_radius / Q
    if not 0 < relative_radius < fmpq(1, 2):
        raise ArithmeticError("The proof of the growth limit needs Re(a) < 1/2")

    mass_fraction = 2 * (1 - inverse_radius / 2)**2 - 1
    if mass_fraction <= 0 or 1 / mass_fraction >= fmpq(1011, 1000):
        raise ArithmeticError("The claimed bound on total mass failed")

    radicand = (1 - relative_radius)**2 + Q * relative_radius**2
    allowance = fmpq(1000108, 1000000) - relative_radius
    if allowance <= 0 or radicand >= allowance**2:
        raise ArithmeticError("The claimed growth bound failed")

    print(f"Mass factor: {arb(1 / mass_fraction).str(18)} < 1.011")
    growth = arb(relative_radius) + arb(radicand).sqrt()
    print(f"Growth factor: {growth.str(18)} < 1.000108")


if __name__ == "__main__":
    ctx.prec = 128
    ctx.cap = 1
    completed_zero_free_rectangle()
    verify_growth_constants()
