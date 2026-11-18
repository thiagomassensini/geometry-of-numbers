#!/usr/bin/env python3
"""Enclose native completed moments and both Hankel pivot towers using FLINT.

Uses the completed expression identified with the original native characteristic
on the strip (CSA NativeScalarZetaIdentification.lean). The Taylor series center
has strip coordinate 1/2. No zeros are used as inputs.
"""

import argparse

from flint import acb, acb_series, arb, ctx


def completed_moments(size):
    # K_size needs h[2*size-1], the coefficient of z**(4*size-1) in R.
    # Differentiate only after retaining the next characteristic coefficient.
    ctx.cap = 4 * size + 2
    z = acb_series([0, 1])
    s = acb(1) / 2 + acb(0, 1) * z
    half = s / 2
    characteristic = s * (s - 1) * (-half * arb.pi().log()).exp()
    characteristic *= half.gamma() * s.zeta() / 2
    if not characteristic[0].real > 0:
        raise ArithmeticError("Constant coefficient of the characteristic is unresolved")
    response = -characteristic.derivative() / (2 * characteristic)
    if response.prec < 4 * size:
        raise ArithmeticError("Logarithmic derivative series is too short")
    moments = []
    for j in range(2 * size):
        coefficient = response[2 * j + 1]
        if not coefficient.real.is_finite() or not coefficient.imag.contains(0):
            raise ArithmeticError(f"Unresolved real moment h[{j}]")
        moments.append(coefficient.real)
    return moments


def hankel_pivots(moments, shift, size):
    # Exact scalar Schur recurrence, with each operation performed on balls.
    matrix = [[moments[i + j + shift] for j in range(size)] for i in range(size)]
    pivots = []
    for k in range(size):
        pivot = matrix[k][k]
        if not pivot > 0:
            raise ArithmeticError(f"Pivot shift={shift}, n={k + 1} unresolved: {pivot.str(12)}")
        pivots.append(pivot)
        for i in range(k + 1, size):
            weight = matrix[i][k] / pivot
            for j in range(i, size):
                updated = matrix[i][j] - weight * matrix[j][k]
                matrix[i][j] = updated
                matrix[j][i] = updated
    return pivots


def center_derivatives(even, odd):
    # The centered-kernel pivot at index r is twice the Hankel pivot
    # selected by parity. Divide by the previous squared slopes.
    slope = None
    product = arb(1)
    for pivot in (p for pair in zip(even, odd) for p in pair):
        new_slope = 2 * pivot / product
        if not new_slope > 0:
            raise ArithmeticError("Unresolved slope from Schur pivots")
        if slope is not None:
            yield slope ** 2 * new_slope
        product *= new_slope ** 2
        slope = new_slope


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--size", type=int, default=16)
    parser.add_argument("--bits", type=int, default=2048)
    args = parser.parse_args()
    if args.size < 1 or args.bits < 32:
        parser.error("--size must be positive and --bits at least 32")
    ctx.prec = args.bits
    moments = completed_moments(args.size)
    even = hankel_pivots(moments, 0, args.size)
    odd = hankel_pivots(moments, 1, args.size)
    derivatives = list(center_derivatives(even, odd))
    print(f"H_1..H_{args.size} and K_1..K_{args.size} are strictly positive ({args.bits} bits)")
    print(f"f_r'(0) is strictly positive for 0 <= r <= {len(derivatives) - 1}")
    if args.size >= 7:
        print(f"K7 Schur pivot: {odd[6].str(16)}")
        print(f"f_12'(0): {derivatives[12].str(16)}")
    print(f"Last even Schur pivot: {even[-1].str(16)}")
    print(f"Last odd Schur pivot: {odd[-1].str(16)}")
    print(f"Last center derivative: {derivatives[-1].str(16)}")


if __name__ == "__main__":
    main()
