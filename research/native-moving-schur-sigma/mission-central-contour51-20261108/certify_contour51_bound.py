#!/usr/bin/env python3
"""Rigorous Arb interval certificate for the radius-51 logarithmic derivative.

This is a computer-assisted certificate, not a Lean theorem.  Every point of
the lower semicircle is covered by one of ARC_COUNT rational parameter arcs.
On each arc, the zeta and zeta-prime ranges are enclosed by a Taylor expansion
at the midpoint plus an explicit Cauchy remainder.  The other terms use Arb
ball arithmetic directly.

The completed native characteristic is xi(1/2 + i*z).  Thus, with
s = 1/2 + i*z and L = xi'(s)/xi(s), the requested response is
R(z) = -i*L/2.  Evenness of the original characteristic makes R odd, so a
bound on the lower semicircle also bounds the upper semicircle.
"""

import argparse
import csv
import platform
from pathlib import Path

import flint
from flint import acb, acb_series, arb, ctx, fmpq


ARC_COUNT = 512
TAYLOR_ORDER = 32
TAYLOR_RADIUS = fmpq(1, 4)
TARGET_LOG_DERIVATIVE = fmpq(8, 5)  # |xi'/xi| < 8/5 implies |R| < 4/5.


def polynomial_value(coefficients, x):
    """Evaluate an Acb coefficient polynomial on an Acb ball."""
    value = acb(0)
    for coefficient in reversed(coefficients):
        value = value * x + coefficient
    return value


def certify_arc(index, pi, log_pi):
    """Return rigorous enclosures for one arc of z = 51*exp(-pi*i*u)."""
    # u covers [index/ARC_COUNT, (index+1)/ARC_COUNT].  Its exact rational
    # midpoint/radius are converted to Arb balls before multiplying by pi.
    u = arb(
        fmpq(2 * index + 1, 2 * ARC_COUNT),
        fmpq(1, 2 * ARC_COUNT),
    )
    angle = -pi * u

    # s = 1/2 + i*z = 1/2 - 51*sin(angle) + 51*i*cos(angle).
    s_arc = acb(arb(fmpq(1, 2)) - 51 * angle.sin(), 51 * angle.cos())
    center = acb(s_arc.real.mid(), s_arc.imag.mid())
    delta = s_arc - center

    radius = arb(TAYLOR_RADIUS)
    delta_upper = delta.abs_upper().upper()
    ratio = (delta_upper / radius).upper()
    if not ratio < 1:
        raise ArithmeticError(f"arc {index}: Taylor disk does not contain arc")

    # The square of half-width 1/4 contains the closed disk of radius 1/4.
    # It also avoids zeta's sole pole at 1; the explicit distance check makes
    # that analyticity condition part of the generated certificate.
    pole_distance_lower = (center - 1).abs_lower().lower()
    if not pole_distance_lower > 1:
        raise ArithmeticError(f"arc {index}: Taylor square may meet zeta's pole")
    square = acb(arb(0, TAYLOR_RADIUS), arb(0, TAYLOR_RADIUS))
    zeta_majorant = ((center + square).zeta().abs_upper()).upper()

    # Cauchy's coefficient estimate |c_k| <= M/r^k gives these tails for
    # zeta and its derivative whenever |delta|/r <= ratio < 1.
    zeta_tail = (
        zeta_majorant * ratio ** (TAYLOR_ORDER + 1) / (1 - ratio)
    ).upper()
    zeta_prime_tail = (
        zeta_majorant
        / radius
        * ratio ** TAYLOR_ORDER
        * ((TAYLOR_ORDER + 1) - TAYLOR_ORDER * ratio)
        / (1 - ratio) ** 2
    ).upper()

    series = acb_series([center, acb(1)], prec=TAYLOR_ORDER + 1).zeta()
    if len(series) != TAYLOR_ORDER + 1:
        raise ArithmeticError(
            f"unexpected Taylor length {len(series)} on arc {index}"
        )
    coefficients = [series[k] for k in range(TAYLOR_ORDER + 1)]
    zeta_polynomial = polynomial_value(coefficients, delta)
    zeta_prime_polynomial = polynomial_value(
        [(k + 1) * coefficients[k + 1] for k in range(TAYLOR_ORDER)],
        delta,
    )

    # A complex error of modulus <= tail lies in this real/imaginary square.
    zeta_arc = zeta_polynomial + acb(arb(0, zeta_tail), arb(0, zeta_tail))
    zeta_prime_arc = zeta_prime_polynomial + acb(
        arb(0, zeta_prime_tail), arb(0, zeta_prime_tail)
    )
    zeta_lower = zeta_arc.abs_lower().lower()
    if not zeta_lower > 0:
        raise ArithmeticError(f"arc {index}: zeta range may contain zero")

    # xi'/xi(s) = 1/s + 1/(s-1) - log(pi)/2
    #             + digamma(s/2)/2 + zeta'(s)/zeta(s).
    log_derivative = (
        1 / s_arc
        + 1 / (s_arc - 1)
        - acb(log_pi / 2)
        + (s_arc / 2).digamma() / 2
        + zeta_prime_arc / zeta_arc
    )
    log_derivative_upper = log_derivative.abs_upper().upper()
    if not (arb(TARGET_LOG_DERIVATIVE) - log_derivative_upper).lower() > 0:
        raise ArithmeticError(
            f"arc {index}: |xi'/xi| bound fails: {log_derivative_upper}"
        )

    response_upper = (log_derivative_upper / 2).upper()
    return {
        "index": index,
        "u_lo": fmpq(index, ARC_COUNT),
        "u_hi": fmpq(index + 1, ARC_COUNT),
        "s_real": s_arc.real,
        "s_imag": s_arc.imag,
        "pole_distance_lower": pole_distance_lower,
        "zeta_lower": zeta_lower,
        "zeta_majorant": zeta_majorant,
        "delta_over_radius_upper": ratio,
        "log_derivative_upper": log_derivative_upper,
        "response_upper": response_upper,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path("C3_ARb_ARCS.csv"),
        help="write all per-arc Arb enclosures to this CSV path",
    )
    args = parser.parse_args()

    ctx.prec = 160
    ctx.cap = TAYLOR_ORDER + 1
    pi = arb.pi()
    log_pi = pi.log()

    rows = [certify_arc(k, pi, log_pi) for k in range(ARC_COUNT)]
    args.csv.parent.mkdir(parents=True, exist_ok=True)
    fields = [
        "index",
        "u_lo",
        "u_hi",
        "s_real",
        "s_imag",
        "pole_distance_lower",
        "zeta_lower",
        "zeta_majorant",
        "delta_over_radius_upper",
        "log_derivative_upper",
        "response_upper",
    ]
    with args.csv.open("w", newline="", encoding="utf-8") as output:
        writer = csv.DictWriter(output, fieldnames=fields)
        writer.writeheader()
        for row in rows:
            writer.writerow({key: str(row[key]) for key in fields})

    max_log_derivative = max(row["log_derivative_upper"] for row in rows)
    max_response = max(row["response_upper"] for row in rows)
    min_zeta_lower = min(row["zeta_lower"] for row in rows)
    max_ratio = max(row["delta_over_radius_upper"] for row in rows)
    if not (arb(fmpq(4, 5)) - max_response).lower() > 0:
        raise ArithmeticError(f"global response bound fails: {max_response}")

    print("C3 radius-51 interval certificate")
    print(f"python={platform.python_version()} python-flint={flint.__version__}")
    print(f"precision_bits={ctx.prec} arcs={ARC_COUNT} Taylor_order={TAYLOR_ORDER}")
    print("covered parameter: u in [0,1], z=51*exp(-pi*i*u)")
    print(f"max |xi'/xi| upper={max_log_derivative}")
    print(f"max |R| upper={max_response}")
    print(f"min |zeta| lower={min_zeta_lower}")
    print(f"max Taylor ratio upper={max_ratio}")
    print("conclusion: |R(z)| < 4/5 on the lower semicircle")
    print("evenness of F gives R(-z)=-R(z), hence the same bound on |z|=51")
    print(f"arc enclosures: {args.csv}")


if __name__ == "__main__":
    main()
