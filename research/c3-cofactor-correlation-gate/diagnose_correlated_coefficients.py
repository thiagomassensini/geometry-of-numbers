#!/usr/bin/env python3
"""Exact-rational correlation diagnostic for the C3 odd 3x3 coefficient gate.

The script propagates the same log(pi) interval through a Horner polynomial,
keeps the certified C3/48 head jets as shared inputs, includes the original
Gamma replacement allowance and C3/48 Cauchy tail, and checks containment in
the candidate boxes already stated in IntervalGate.lean.  This remains a
reproducible diagnostic; the intended Lean theorem must establish the same
crosswalk and enclosures before this can be called a certificate.
"""
from __future__ import annotations

import math
import re
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TASK = ROOT / "research/c3-cofactor-chiral-certification"
PRIMITIVES = ROOT / "research/c3-fourteenth-tail/CompletionPrimitiveBoxes.lean"


def block(path: Path, first: str, next_: str) -> str:
    source = path.read_text()
    start = source.index(first)
    return source[start : source.index(next_, start)]


def denominator(text: str) -> int:
    return 10 ** int(text[3:]) if text.startswith("10^") else int(text)


def pairs(source: str) -> list[tuple[F, F]]:
    found = re.findall(
        r"⟨\(?(-?\d+)\s*/\s*(10\^\d+|\d+)\)?,\s*"
        r"\(?(-?\d+)\s*/\s*(10\^\d+|\d+)\)?⟩",
        source,
    )
    return [
        (F(int(a), denominator(b)), F(int(c), denominator(d)))
        for a, b, c, d in found
    ]


def values(source: str) -> list[F]:
    return [F(int(a), denominator(b)) for a, b in re.findall(r"(-?\d+)\s*/\s*(10\^\d+|\d+)", source)]


def box_definition(source: str, name: str) -> tuple[F, F]:
    match = re.search(
        rf"def {name} : Box := ⟨\(([-\d]+)/([\d]+)\),\s*"
        rf"\(([-\d]+)/([\d]+)\)⟩",
        source,
    )
    if match is None:
        raise ValueError(f"could not parse {name}")
    return F(int(match[1]), int(match[2])), F(int(match[3]), int(match[4]))


def add(x: tuple[F, F], y: tuple[F, F]) -> tuple[F, F]:
    return x[0] + y[0], x[1] + y[1]


def neg(x: tuple[F, F]) -> tuple[F, F]:
    return -x[1], -x[0]


def sub(x: tuple[F, F], y: tuple[F, F]) -> tuple[F, F]:
    return add(x, neg(y))


def mul(x: tuple[F, F], y: tuple[F, F]) -> tuple[F, F]:
    products = [a * b for a in x for b in y]
    return min(products), max(products)


def inv(x: tuple[F, F]) -> tuple[F, F]:
    if x[0] <= 0 <= x[1]:
        raise ValueError("interval reciprocal contains zero")
    return F(1, 1) / x[1], F(1, 1) / x[0]


def div(x: tuple[F, F], y: tuple[F, F]) -> tuple[F, F]:
    return mul(x, inv(y))


def power(x: tuple[F, F], n: int) -> tuple[F, F]:
    result = (F(1), F(1))
    for _ in range(n):
        result = mul(result, x)
    return result


def scale(x: tuple[F, F], q: F) -> tuple[F, F]:
    return mul(x, (q, q))


def total(xs) -> tuple[F, F]:
    result = (F(0), F(0))
    for x in xs:
        result = add(result, x)
    return result


def horner(coefficients: list[tuple[F, F]], x: tuple[F, F]) -> tuple[F, F]:
    result = (F(0), F(0))
    for coefficient in reversed(coefficients):
        result = add(mul(result, x), coefficient)
    return result


def decimal(q: F, digits: int = 36) -> str:
    from decimal import Decimal, localcontext

    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def main() -> None:
    head = pairs(block(TASK / "C3Head48Boxes.lean", "def head48ReferenceBox", "theorem head48_evaluator_check"))
    gamma = values(block(TASK / "GammaThirteen.lean", "def gammaRealReference13", "def gammaRationalPolynomial13"))
    gamma0 = gamma[0]
    gamma_normalized = [(x / gamma0, x / gamma0) for x in gamma]
    primitive_text = PRIMITIVES.read_text()
    pi_amplitude = box_definition(primitive_text, "piAmplitudeReference")
    pi_log = box_definition(primitive_text, "piLogReference")
    chart = pairs(block(TASK / "CompletedBoxes48.lean", "def chartAmplitudeReferenceTight", "theorem chart_amplitude_tight_contains"))[0]

    gamma_text = (TASK / "GammaThirteen.lean").read_text()
    log_match = re.search(r"def logReferenceTight : ℚ :=\s*(\d+)\s*/\s*(10\^\d+|\d+)", gamma_text)
    if log_match is None:
        raise ValueError("could not parse logReferenceTight")
    log_center = F(int(log_match[1]), denominator(log_match[2]))
    log_radius = F(1, 10**44)
    log_three = (log_center - log_radius, log_center + log_radius)
    q_chart = div(chart, sub((F(1), F(1)), chart))

    # D(t)=1+q(1-exp(-ell*t)); the normalized chart reciprocal is 1/D(t).
    denominator_jet = [(F(1), F(1))]
    for n in range(1, 13):
        denominator_jet.append(
            scale(mul(q_chart, power(log_three, n)), F((-1) ** (n + 1), math.factorial(n)))
        )
    reciprocal_jet = [(F(1), F(1))]
    for n in range(1, 13):
        reciprocal_jet.append(
            neg(total(mul(reciprocal_jet[n - j], denominator_jet[j]) for j in range(1, n + 1)))
        )

    # P(t)=1-4t^2. The shared log(pi) variable is kept as the Horner argument.
    polynomial = [F(0)] * 13
    polynomial[0], polynomial[2] = F(1), F(-4)
    base_polynomial: list[list[tuple[F, F]]] = []
    for n in range(13):
        coefficients = [(F(0), F(0)) for _ in range(n + 1)]
        for i in range(n + 1):
            for r in range(n - i + 1):
                e = n - i - r
                factor = F(polynomial[i] * (-1) ** e, 2**e * math.factorial(e))
                coefficients[e] = add(coefficients[e], scale(reciprocal_jet[r], factor))
        base_polynomial.append(coefficients)

    full_polynomial: list[list[tuple[F, F]]] = []
    for n in range(13):
        coefficients = [(F(0), F(0)) for _ in range(n + 1)]
        for gamma_order in range(n + 1):
            for e, coefficient in enumerate(base_polynomial[n - gamma_order]):
                coefficients[e] = add(coefficients[e], scale(coefficient, gamma_normalized[gamma_order][0]))
        full_polynomial.append(coefficients)

    base_jet = [horner(coefs, pi_log) for coefs in base_polynomial]
    full_jet = [horner(coefs, pi_log) for coefs in full_polynomial]
    reciprocal_chart_zero = inv(sub((F(1), F(1)), chart))
    source_scale = mul(
        mul(scale(pi_amplitude, F(-1, 8)), reciprocal_chart_zero),
        (gamma0, gamma0),
    )
    left_scale = mul(scale(pi_amplitude, F(-1, 8)), reciprocal_chart_zero)

    # Propagate the original left jets too, then evaluate the exact Gamma
    # replacement ledger from GammaHeadCrosswalk rather than assuming a bound.
    left_real_jet: list[tuple[F, F]] = []
    for n in range(13):
        normalized_left = total(mul(head[k], base_jet[n - k]) for k in range(n + 1))
        left_real_jet.append(mul(left_scale, normalized_left))
    left_abs = [max(abs(lo), abs(hi)) for lo, hi in left_real_jet]
    if any(x > 3 for x in left_abs):
        raise AssertionError("left-jet bound required for the Gamma ledger failed")
    print("left-jet absolute bounds from the shared exact-rational enclosure:")
    for j, value in enumerate(left_abs):
        grid = 10**6
        bound = F((value * grid).numerator // (value * grid).denominator + 1, grid)
        print(f"  j={j}: < {bound.numerator}/{bound.denominator} ({decimal(bound)})")
    left_abs_total = sum(left_abs, F(0))
    print(f"sum of 13 absolute bounds: {decimal(left_abs_total)}")
    gamma_error = max(
        sum(left_abs[: r + 1], F(0)) / 10**24 for r in range(13)
    )
    tail_order12 = F(96 * math.factorial(26) * 4**12, 729**2 * 143**25)
    if not tail_order12 < F(2, 10**24):
        raise AssertionError("unexpected C3/48 tail bound")
    transport_error = gamma_error + F(2, 10**24)

    candidate_source = (TASK / "IntervalGate.lean").read_text()
    print(f"scale interval: [{decimal(source_scale[0])}, {decimal(source_scale[1])}]")
    print(f"C3/48 order-12 tail < {decimal(tail_order12)}")
    print(f"maximum exact Gamma replacement allowance: {decimal(gamma_error)}")
    print(f"uniform Gamma + tail allowance used: {decimal(transport_error)}")
    print("candidate coefficient containment (exact rational endpoints):")
    smallest_slack = None
    for j in range(7):
        normalized = total(
            scale(mul(head[k], full_jet[2 * j - k]), F((-1) ** j))
            for k in range(2 * j + 1)
        )
        finite_reference = mul(source_scale, normalized)
        source_interval = (finite_reference[0] - transport_error, finite_reference[1] + transport_error)
        match = re.search(rf"\| {j} => ⟨([^,]+),\s*([^⟩]+)⟩", candidate_source)
        if match is None:
            raise ValueError(f"could not parse candidateCoefficientBall {j}")
        center_pair = re.search(r"(-?\d+)\s*/\s*(10\^\d+|\d+)", match[1])
        radius_pair = re.search(r"(-?\d+)\s*/\s*(10\^\d+|\d+)", match[2])
        center = F(int(center_pair[1]), denominator(center_pair[2]))
        radius = F(int(radius_pair[1]), denominator(radius_pair[2]))
        candidate = (center - radius, center + radius)
        slack = min(source_interval[0] - candidate[0], candidate[1] - source_interval[1])
        contained = slack >= 0
        smallest_slack = slack if smallest_slack is None else min(smallest_slack, slack)
        print(
            f"  c{j}: source=[{decimal(source_interval[0])}, {decimal(source_interval[1])}], "
            f"inside={contained}, slack={decimal(slack, 12)}"
        )
        if not contained:
            raise AssertionError(f"candidate coefficient box {j} is too narrow")

    print(f"minimum candidate slack: {decimal(smallest_slack, 16)}")
    print("classification: exact-rational diagnostic; Lean source crosswalk is proved in SourceCoefficientGreen.lean.")


if __name__ == "__main__":
    main()
