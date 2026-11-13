#!/usr/bin/env python3
"""Exact rational regressions for the division-free Hankel residual.

This is an independent finite check of the algebra in ResidualPadé.lean.  The
review's original verifier and JSON were not present in this workspace, so the
five deterministic sequence families below reconstruct its stated dimensions,
shifts, and case counts; they do not claim to reproduce its hidden inputs.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from random import Random


SHIFTS = (0, 1, 3)
ORDERS = tuple(range(8))


def determinant(matrix: list[list[Fraction]]) -> Fraction:
    """Fraction-preserving Gaussian elimination, with det([]) = 1."""
    size = len(matrix)
    if any(len(row) != size for row in matrix):
        raise ValueError("determinant expects a square matrix")
    work = [[Fraction(x) for x in row] for row in matrix]
    result = Fraction(1)
    for column in range(size):
        pivot = next((row for row in range(column, size) if work[row][column]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            result = -result
        diagonal = work[column][column]
        result *= diagonal
        for row in range(column + 1, size):
            factor = work[row][column] / diagonal
            for entry in range(column + 1, size):
                work[row][entry] -= factor * work[column][entry]
    return result


def solve(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction]:
    """Solve an invertible rational square system by exact elimination."""
    size = len(matrix)
    if size != len(rhs):
        raise ValueError("matrix and rhs dimensions differ")
    work = [[Fraction(x) for x in row] + [Fraction(rhs[i])]
            for i, row in enumerate(matrix)]
    for column in range(size):
        pivot = next((row for row in range(column, size) if work[row][column]), None)
        if pivot is None:
            raise ValueError("solve requires an invertible matrix")
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
        diagonal = work[column][column]
        work[column] = [entry / diagonal for entry in work[column]]
        for row in range(size):
            if row == column:
                continue
            factor = work[row][column]
            work[row] = [x - factor * y for x, y in zip(work[row], work[column])]
    return [work[row][-1] for row in range(size)]


def minor(matrix: list[list[Fraction]], row: int, column: int) -> list[list[Fraction]]:
    return [
        [entry for j, entry in enumerate(line) if j != column]
        for i, line in enumerate(matrix)
        if i != row
    ]


def families() -> dict[str, list[Fraction]]:
    max_index = 17
    positive = [
        sum((Fraction(node**k) for node in range(1, 10)), Fraction(0))
        for k in range(max_index + 1)
    ]
    signed = [
        sum((Fraction((-1) ** i * (i + 1) * (i + 2) ** k)
             for i in range(9)), Fraction(0))
        for k in range(max_index + 1)
    ]

    rng = Random(120)
    arbitrary = [Fraction(rng.randint(-9, 9), rng.randint(1, 7))
                 for _ in range(max_index + 1)]
    if arbitrary[0] == 0:
        arbitrary[0] = Fraction(1, 3)

    rank_one = [Fraction(1) for _ in range(max_index + 1)]
    zero = [Fraction(0) for _ in range(max_index + 1)]
    return {
        "positive_moments": positive,
        "signed_moments": signed,
        "arbitrary_rational": arbitrary,
        "rank_one_constant": rank_one,
        "zero_sequence": zero,
    }


def check_case(name: str, moments: list[Fraction], shift: int, order: int) -> dict[str, object]:
    prefix = [
        [moments[shift + i + j] for j in range(order)]
        for i in range(order)
    ]
    coupling = [moments[shift + order + i] for i in range(order)]
    tau = determinant(prefix)

    # adj(G)b, written by signed minors so no inverse is used in this check.
    cofactor_vector = []
    for i in range(order):
        adjugate_times_coupling = sum(
            (Fraction((-1) ** (j + i)) * determinant(minor(prefix, j, i)) * coupling[j]
             for j in range(order)),
            Fraction(0),
        )
        cofactor_vector.append(-adjugate_times_coupling)
    cofactor_vector.append(tau)

    border = [
        [moments[shift + i + j] for j in range(order + 1)]
        for i in range(order + 1)
    ]
    border_det = determinant(border)
    border_product = [
        sum((border[i][j] * cofactor_vector[j] for j in range(order + 1)), Fraction(0))
        for i in range(order + 1)
    ]
    expected_border_product = [Fraction(0)] * order + [border_det]
    if border_product != expected_border_product:
        raise AssertionError(f"{name}, s={shift}, n={order}: H*w identity failed")

    # Dbar has the fixed n+1 coefficients w_n,...,w_0, including zeros.
    denominator = [cofactor_vector[order - degree] for degree in range(order + 1)]
    product = []
    for degree in range(2 * order + 1):
        product.append(sum(
            (denominator[i] * moments[shift + degree - i]
             for i in range(min(order, degree) + 1)),
            Fraction(0),
        ))
    numerator = [product[k] if k < order else Fraction(0)
                 for k in range(2 * order + 1)]
    defect = [product[k] - numerator[k] for k in range(2 * order + 1)]
    if any(defect[k] != 0 for k in range(2 * order)):
        raise AssertionError(f"{name}, s={shift}, n={order}: low defect coefficient failed")
    if defect[2 * order] != border_det:
        raise AssertionError(f"{name}, s={shift}, n={order}: leading defect coefficient failed")

    # Generate C from the exact recurrence C*M = -C' with c_0 = 2.
    residual_degree = 2 * order + shift
    characteristic = [Fraction(2)]
    for k in range(residual_degree + 1):
        convolution = sum(
            (characteristic[i] * moments[k - i] for i in range(k + 1)),
            Fraction(0),
        )
        characteristic.append(-convolution / (k + 1))

    prefix_series = [moments[k] if k < shift else Fraction(0)
                     for k in range(residual_degree + 1)]
    numerator_shifted = [
        numerator[k - shift] if shift <= k and k - shift < order else Fraction(0)
        for k in range(residual_degree + 1)
    ]
    correction = []
    for degree in range(residual_degree + 1):
        d_times_prefix = sum(
            (denominator[i] * prefix_series[degree - i]
             for i in range(min(order, degree) + 1)),
            Fraction(0),
        )
        correction.append(d_times_prefix + numerator_shifted[degree])

    residual = []
    for degree in range(residual_degree + 1):
        derivative_product = sum(
            (denominator[i] * (degree - i + 1) * characteristic[degree - i + 1]
             for i in range(min(order, degree) + 1)),
            Fraction(0),
        )
        correction_product = sum(
            (correction[i] * characteristic[degree - i]
             for i in range(degree + 1)),
            Fraction(0),
        )
        residual.append(-derivative_product - correction_product)

    if any(residual[k] != 0 for k in range(residual_degree)):
        raise AssertionError(f"{name}, s={shift}, n={order}: transported low coefficient failed")
    expected_residual = characteristic[0] * border_det
    if residual[residual_degree] != expected_residual:
        raise AssertionError(f"{name}, s={shift}, n={order}: transported leading coefficient failed")

    if tau:
        solved = solve(prefix, coupling)
        pivot = moments[shift + 2 * order] - sum(
            (coupling[i] * solved[i] for i in range(order)), Fraction(0)
        )
        if border_det / tau != pivot:
            raise AssertionError(f"{name}, s={shift}, n={order}: Schur quotient failed")
        if residual[residual_degree] / tau != characteristic[0] * pivot:
            raise AssertionError(f"{name}, s={shift}, n={order}: normalized residual failed")

    return {
        "family": name,
        "shift": shift,
        "order": order,
        "prefix_invertible": bool(tau),
        "empty_prefix": order == 0,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exact", action="store_true", help="run all rational checks")
    parser.add_argument("--out", type=Path, help="write a JSON summary")
    args = parser.parse_args()
    if not args.exact:
        parser.error("pass --exact to run the rational regression suite")

    cases = [
        check_case(name, sequence, shift, order)
        for name, sequence in families().items()
        for shift in SHIFTS
        for order in ORDERS
    ]
    invertible = sum(case["prefix_invertible"] for case in cases)
    singular = len(cases) - invertible
    empty = sum(case["empty_prefix"] for case in cases)
    summary: dict[str, object] = {
        "suite": "independent exact rational reconstruction of the residual checks",
        "cases": len(cases),
        "invertible_prefixes": invertible,
        "singular_prefixes": singular,
        "empty_prefix_cases": empty,
        "by_family": {
            name: {
                "cases": sum(case["family"] == name for case in cases),
                "invertible_prefixes": sum(
                    case["family"] == name and case["prefix_invertible"] for case in cases
                ),
                "singular_prefixes": sum(
                    case["family"] == name and not case["prefix_invertible"] for case in cases
                ),
            }
            for name in families()
        },
        "checks": [
            "H*w = (0,...,0,det(H))",
            "all Dbar*Q_s-Nbar coefficients below 2n vanish",
            "coefficient 2n equals det(H)",
            "transported residual coefficients below 2n+s vanish",
            "transported coefficient 2n+s equals c0*det(H)",
            "invertible cases satisfy det(H)/det(G) = Schur pivot",
        ],
    }
    if (len(cases), invertible, singular, empty) != (120, 81, 39, 15):
        raise AssertionError(f"unexpected regression coverage: {summary}")

    rendered = json.dumps(summary, indent=2, sort_keys=True)
    print(rendered)
    if args.out:
        args.out.write_text(rendered + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
