#!/usr/bin/env python3
"""Exact rational conditioning check for interpolation of the even C5 source."""
from fractions import Fraction
from pathlib import Path

N = 128
STEP = Fraction(1, 100_000)
OUTER = Fraction(38, 100)
SOURCE_BOUND = 10**100
GAMMA_ERROR = Fraction(1, 10**259)
MAX_DEGREE = 14


def lagrange_coefficients(node: int) -> list[Fraction]:
    """Coefficients in x of the Lagrange basis at node^2 among 0^2..N^2."""
    polynomial = [1]
    denominator = 1
    for other in range(N + 1):
        if other == node:
            continue
        root = other * other
        product = [0] * (len(polynomial) + 1)
        for degree, coefficient in enumerate(polynomial):
            product[degree] -= root * coefficient
            product[degree + 1] += coefficient
        polynomial = product
        denominator *= node * node - root
    return [Fraction(coefficient, denominator) for coefficient in polynomial]


all_coefficients = [lagrange_coefficients(j) for j in range(N + 1)]
weight_sums = []
for degree in range(MAX_DEGREE + 1):
    weight_sum = sum(
        (abs(all_coefficients[j][degree]) * STEP ** (-2 * degree)
         for j in range(N + 1)),
        Fraction(0),
    )
    weight_sums.append(weight_sum)
    assert weight_sum < 10**124

ratio = (N * STEP / OUTER) ** 2
assert ratio < 1
analytic_tail = Fraction(SOURCE_BOUND) * ratio ** (N + 1) / (1 - ratio)
for weight_sum in weight_sums:
    assert weight_sum * analytic_tail < Fraction(1, 10**410)
    assert weight_sum * GAMMA_ERROR < Fraction(1, 10**135)

print(f"nodes=0..{N}; step=1/100000; t_max={N * STEP}")
print(f"outer radius={OUTER}; assumed analytic modulus bound={SOURCE_BOUND}")
print(f"max exact sum_j |lambda[j,n]| for n<=14 < 10^124")
print(f"max exact interpolation tail contribution for n<=14 < 10^-410")
print(f"max exact amplification of Gamma error 10^-259 < 10^-135")
print("exact per-degree rational weight-sum bounds:")
for degree, weight_sum in enumerate(weight_sums):
    exponent = 0
    while weight_sum >= 10**exponent:
        exponent += 1
    print(f"n={degree}: sum_j |lambda[j,n]| < 10^{exponent}")
