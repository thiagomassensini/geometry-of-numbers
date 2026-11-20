#!/usr/bin/env python3
"""Enclose both centered Schur towers from the camera-free theta integral."""

import argparse
from math import factorial

from flint import acb, arb, ctx


def raw_even_coefficients(count, cutoff, terms):
    pi = arb.pi()
    end = arb(cutoff)
    tolerance = arb(2)**(20 - ctx.prec)
    endpoint_scale = (2 * end).exp()
    frequencies = [pi * n**2 for n in range(1, terms + 1)]

    # Bound all terms in the real tail by the first exponential in each variable.
    gaussian_sum_bound = (-pi / 2).exp() / (1 - 16 * (-3 * pi / 2).exp())
    if not gaussian_sum_bound < 1:
        raise ArithmeticError("Cannot bound the Gaussian sum by one")
    first_skipped = terms + 1
    finite_strip_tail = (
        4 * pi**2 * end * (arb(9) * end / 2).exp()
        * first_skipped**4 * (-pi * first_skipped**2).exp()
        / (1 - 16 * (-pi * (2 * first_skipped + 1)).exp())
    )

    for j in range(count):
        degree = 2 * j

        def integrand(y, _analytic):
            scale = (2 * y).exp()
            radial = (5 * y / 2).exp()
            # The truncated integrand is entire in the integration variable.
            total = acb(0)
            for frequency in frequencies:
                wave = frequency * scale
                total += (2 * wave - 3) * frequency * (-wave).exp()
            return 2 * radial * y**degree * total

        head = acb.integral(
            integrand, 0, cutoff, rel_tol=tolerance, abs_tol=tolerance,
            eval_limit=100000,
        )
        if not head.real.is_finite() or not head.imag.contains(0):
            raise ArithmeticError(f"Unresolved integral coefficient {j}")

        exponent = arb(9) / 2 + degree
        decay = pi * endpoint_scale - exponent
        if not decay > 0:
            raise ArithmeticError(f"Integration cutoff too small for coefficient {j}")
        real_line_tail = 4 * pi**2 * (exponent * end - pi * endpoint_scale / 2).exp() / decay
        remainder = (finite_strip_tail * end**degree + real_line_tail).upper()
        coefficient = 2 * (head.real + arb(0, remainder)) / factorial(degree)
        if not coefficient > 0:
            raise ArithmeticError(f"Unresolved sign of coefficient {j}")
        yield coefficient


def bezout_block(terms, size, sector):
    matrix = [[arb(0) for _ in range(size)] for _ in range(size)]
    for i in range(size):
        for j in range(i, size):
            value = arb(0)
            for k in range(j + 1):
                a, b = i + 1 + k, j - k
                if sector == 0:
                    value += (b - a) * terms[a] * terms[b]
                else:
                    value += (b + 1) * terms[a] * terms[b+1] - (a + 1) * terms[a+1] * terms[b]
            matrix[i][j] = matrix[j][i] = value
    return matrix


def schur_pivots(matrix, sector, scale):
    for k in range(len(matrix)):
        pivot = matrix[k][k]
        if not pivot > 0:
            raise ArithmeticError(f"Unresolved pivot at sector={sector}, degree={k}: {pivot.str(12)}")
        yield pivot / scale**(2*k + sector + 1)
        for i in range(k + 1, len(matrix)):
            multiplier = matrix[i][k] / pivot
            for j in range(i, len(matrix)):
                value = matrix[i][j] - multiplier * matrix[j][k]
                matrix[i][j] = matrix[j][i] = value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--size", type=int, default=12)
    parser.add_argument("--bits", type=int, default=640)
    parser.add_argument("--terms", type=int, default=13)
    parser.add_argument("--cutoff", type=int, default=4)
    args = parser.parse_args()
    if args.size < 1 or args.bits < 64 or args.terms < 1 or args.cutoff < 1:
        parser.error("Size, terms and cutoff must be positive, with at least 64 bits")

    ctx.prec = args.bits
    coefficients = list(raw_even_coefficients(2 * args.size + 1, args.cutoff, args.terms))
    scale = arb(196)
    terms = [(-scale)**j * value / coefficients[0] for j, value in enumerate(coefficients)]
    print(f"F(1/2) from theta: {coefficients[0].str(16)}", flush=True)
    for sector in (0, 1):
        matrix = bezout_block(terms, args.size, sector)
        for n, pivot in enumerate(schur_pivots(matrix, sector, scale)):
            print(f"sector={sector} degree={n} completed pivot={pivot.str(16)}", flush=True)


if __name__ == "__main__":
    main()
