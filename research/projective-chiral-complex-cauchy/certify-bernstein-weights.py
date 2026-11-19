from math import comb
from pathlib import Path
from runpy import run_path

from flint import arb, ctx, fmpq


C3 = run_path(str(Path(__file__).with_name("certify-c3-last-coefficient.py")))
Q = fmpq(22, 175)
CHECKS = ((1, 32), (1, 64), (1, 115), (6, 110), (20, 96))


def bernstein_weights(moments, shift, degree):
    """L_s of the Bernstein basis on [0,q], via forward differences."""
    q = arb(Q)
    row = [moments[shift + j] / q ** j for j in range(degree + 1)]
    descending_weights = [row[-1]]
    for k in range(degree - 1, -1, -1):
        row = [left - right for left, right in zip(row, row[1:])]
        descending_weights.append(comb(degree, k) * row[-1])
    return list(reversed(descending_weights))


def check_row(moments, shift, degree):
    weights = bernstein_weights(moments, shift, degree)
    if not sum(weights).overlaps(moments[shift]):
        raise ArithmeticError("Bernstein mass disagrees with the shifted moment")
    for j in (1, 2, 5, 10):
        reconstructed = sum(
            weight * fmpq(comb(k, j), comb(degree, j))
            for k, weight in enumerate(weights) if k >= j
        ) * arb(Q) ** j
        if not reconstructed.overlaps(moments[shift + j]):
            raise ArithmeticError("Bernstein factorial reconstruction disagrees")
    minimum = min(weight.lower() for weight in weights)
    if not minimum > 0:
        raise ArithmeticError(f"Bernstein weight positivity unresolved at {shift=}, {degree=}")
    print(f"{shift},{degree},{minimum.str(9)},{sum(abs(w) for w in weights).str(12)}", flush=True)


def main():
    ctx.prec = 6144
    count = max(shift + degree for shift, degree in CHECKS) + 2
    moments = C3["prefix_moments"](C3["recomposed_c3_coefficients"](count))
    print("shift,Bernstein degree,minimum lower bound,total variation", flush=True)
    for shift, degree in CHECKS:
        check_row(moments, shift, degree)


if __name__ == "__main__":
    main()
