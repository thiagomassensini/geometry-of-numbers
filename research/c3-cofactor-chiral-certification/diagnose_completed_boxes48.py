#!/usr/bin/env python3
"""Exact Fraction diagnostic for the M=48 reference-jet cofactor interval.

This reads the rational endpoints from the Lean source tables and repeats the
same interval recurrences with Python's exact fractions.  It diagnoses whether
these reference boxes can certify the odd third pivot.  The calculation does
not include the native-Gamma replacement error, so it is not a source sign
certificate; the Lean containment theorems remain the formal enclosure proof.
"""

from __future__ import annotations

import re
from fractions import Fraction
from pathlib import Path

Interval = tuple[Fraction, Fraction]
ROOT = Path(__file__).resolve().parents[2]
TASK = ROOT / "research/c3-cofactor-chiral-certification"


def block(path: Path, first: str, next_: str) -> str:
    source = path.read_text()
    start = source.index(first)
    return source[start : source.index(next_, start)]


def denominator(text: str) -> int:
    return 10 ** int(text[3:]) if text.startswith("10^") else int(text)


def rational_pairs(source: str) -> list[tuple[Fraction, Fraction]]:
    found = re.findall(
        r"⟨\(?(-?\d+)\s*/\s*(10\^\d+|\d+)\)?,\s*"
        r"\(?(-?\d+)\s*/\s*(10\^\d+|\d+)\)?⟩",
        source,
    )
    return [
        (Fraction(int(a), denominator(b)), Fraction(int(c), denominator(d)))
        for a, b, c, d in found
    ]


def rational_values(source: str) -> list[Fraction]:
    found = re.findall(r"(-?\d+)\s*/\s*(10\^\d+|\d+)", source)
    return [Fraction(int(a), denominator(b)) for a, b in found]


def point(value: Fraction | int) -> Interval:
    q = Fraction(value)
    return q, q


def add(x: Interval, y: Interval) -> Interval:
    return x[0] + y[0], x[1] + y[1]


def neg(x: Interval) -> Interval:
    return -x[1], -x[0]


def sub(x: Interval, y: Interval) -> Interval:
    return add(x, neg(y))


def mul(x: Interval, y: Interval) -> Interval:
    products = [a * b for a in x for b in y]
    return min(products), max(products)


def inv(x: Interval) -> Interval:
    if x[0] <= 0 <= x[1]:
        raise ValueError("reciprocal interval contains zero")
    return Fraction(1, 1) / x[1], Fraction(1, 1) / x[0]


def power(x: Interval, n: int) -> Interval:
    result = point(1)
    for _ in range(n):
        result = mul(result, x)
    return result


def convolution(a: list[Interval], b: list[Interval], n: int) -> Interval:
    result = point(0)
    for j in range(n + 1):
        result = add(result, mul(a[j], b[n - j]))
    return result


def box_definition(source: str, name: str) -> Interval:
    match = re.search(
        rf"def {name} : Box := ⟨\(([-\d]+)/(\d+)\),\s*"
        rf"\(([-\d]+)/(\d+)\)⟩",
        source,
    )
    if match is None:
        raise ValueError(f"could not parse Lean box {name}")
    return Fraction(int(match[1]), int(match[2])), Fraction(int(match[3]), int(match[4]))


def decimal(q: Fraction, digits: int = 38) -> str:
    # This is display only; all interval operations and zero comparisons above
    # are performed on exact rational numbers.
    from decimal import Decimal, localcontext

    with localcontext() as ctx:
        ctx.prec = digits
        return str(Decimal(q.numerator) / Decimal(q.denominator))


def main() -> None:
    head_source = block(
        TASK / "C3Head48Boxes.lean", "def head48ReferenceBox", "theorem head48_evaluator_check"
    )
    head = rational_pairs(head_source)
    gamma_source = block(
        TASK / "GammaThirteen.lean", "def gammaRealReference13", "def gammaRationalPolynomial13"
    )
    gamma_values = rational_values(gamma_source)
    gamma = [(q, q) for q in gamma_values]

    completion_source = (ROOT / "research/c3-fourteenth-tail/CompletionPrimitiveBoxes.lean").read_text()
    pi_amplitude = box_definition(completion_source, "piAmplitudeReference")
    pi_log = box_definition(completion_source, "piLogReference")

    gamma_file = TASK / "GammaThirteen.lean"
    log_definition = re.search(
        r"def logReferenceTight : ℚ :=\s*(\d+)\s*/\s*(10\^\d+|\d+)",
        gamma_file.read_text(),
    )
    if log_definition is None:
        raise ValueError("could not parse logReferenceTight from GammaThirteen.lean")
    log_reference = Fraction(int(log_definition[1]), denominator(log_definition[2]))
    log3 = (log_reference - Fraction(1, 10**44), log_reference + Fraction(1, 10**44))
    chart_source = block(
        TASK / "CompletedBoxes48.lean",
        "def chartAmplitudeReferenceTight",
        "theorem chart_amplitude_tight_contains",
    )
    chart_amplitude = rational_pairs(chart_source)[0]

    polynomial = [point(Fraction(-1, 8))] + [
        point(Fraction(1, 2) if r == 2 else 0) for r in range(1, 13)
    ]
    exponential: list[Interval] = []
    chart: list[Interval] = []
    for r in range(13):
        factorial = point(Fraction(1, __import__("math").factorial(r)))
        exponential.append(
            mul(pi_amplitude, mul(power(mul(point(Fraction(-1, 2)), pi_log), r), factorial))
        )
        chart_constant = point(1 if r == 0 else 0)
        chart.append(
            sub(chart_constant, mul(chart_amplitude, mul(power(neg(log3), r), factorial)))
        )

    reciprocal = [inv(chart[0])]
    for n in range(12):
        total = point(0)
        for j in range(n + 1):
            total = add(total, mul(reciprocal[j], chart[n + 1 - j]))
        reciprocal.append(mul(neg(total), inv(chart[0])))

    polynomial_exponential = [convolution(polynomial, exponential, n) for n in range(13)]
    with_reciprocal = [convolution(polynomial_exponential, reciprocal, n) for n in range(13)]
    with_head = [convolution(with_reciprocal, head, n) for n in range(13)]
    completed_reference = [convolution(with_head, gamma, n) for n in range(13)]

    # For F(z)=C(z²), c_j is (-1)^j times the real even jet because the source
    # variable includes the original i-phase.  The completion tail radius is
    # the already-proved M=48 bound, added symmetrically here.
    tail = Fraction(1, 10**20)
    coefficients: list[Interval] = []
    for j in range(7):
        coefficient = completed_reference[2 * j]
        if j % 2:
            coefficient = neg(coefficient)
        coefficients.append((coefficient[0] - tail, coefficient[1] + tail))

    c = coefficients
    two = point(2)
    three = point(3)
    four = point(4)
    five = point(5)
    six = point(6)
    a = sub(mul(c[1], c[1]), mul(two, mul(c[0], c[2])))
    b = sub(mul(c[1], c[2]), mul(three, mul(c[0], c[3])))
    d = sub(
        mul(two, mul(c[2], c[2])),
        add(mul(two, mul(c[1], c[3])), mul(four, mul(c[0], c[4]))),
    )
    e = sub(mul(c[1], c[3]), mul(four, mul(c[0], c[4])))
    f = sub(
        sub(mul(two, mul(c[2], c[3])), mul(three, mul(c[1], c[4]))),
        mul(five, mul(c[0], c[5])),
    )
    g = sub(
        sub(sub(mul(three, mul(c[3], c[3])), mul(two, mul(c[2], c[4]))),
            mul(four, mul(c[1], c[5]))),
        mul(six, mul(c[0], c[6])),
    )

    x = point(Fraction(14879782871, 10**14))
    y = point(Fraction(1692226107996, 10**14))
    prefix = sub(mul(a, d), mul(b, b))
    residual0 = add(add(mul(a, x), mul(b, y)), e)
    residual1 = add(add(mul(b, x), mul(d, y)), f)
    energy = add(
        add(
            add(
                add(
                    add(mul(a, mul(x, x)), mul(two, mul(mul(b, x), y))),
                    mul(d, mul(y, y)),
                ),
                mul(two, mul(e, x)),
            ),
            mul(two, mul(f, y)),
        ),
        g,
    )
    adjugate = add(
        sub(mul(d, mul(residual0, residual0)),
            mul(two, mul(b, mul(residual0, residual1)))),
        mul(a, mul(residual1, residual1)),
    )
    margin = sub(mul(prefix, energy), adjugate)

    print("Exact Fraction diagnostic: M=48 finite Gamma-reference head + tail radius.")
    print("Native-Gamma replacement error is not included in these boxes.")
    for j, interval in enumerate(coefficients):
        print(
            f"c{j}: [{decimal(interval[0])}, {decimal(interval[1])}] "
            f"width={decimal(interval[1] - interval[0], 12)}"
        )
    print(f"cofactor margin: [{decimal(margin[0])}, {decimal(margin[1])}]")
    print(f"contains zero: {margin[0] <= 0 <= margin[1]}")


if __name__ == "__main__":
    main()
