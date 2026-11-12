#!/usr/bin/env python3
"""Emit compact rational table entries for the Lean interval certificate.

All calculations use Fraction endpoints and the exact Box arithmetic from
CompletedBoxes48.lean. Chart reciprocal tables use 1e-30 outward rounding;
later coefficient tables use 1e-24. Lean rechecks each table containment.
"""
from __future__ import annotations

import math
import re
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TASK = ROOT / "research/c3-cofactor-chiral-certification"
PRIMITIVES = ROOT / "research/c3-fourteenth-tail/CompletionPrimitiveBoxes.lean"


def section(path: Path, start: str, stop: str) -> str:
    text = path.read_text()
    i = text.index(start)
    return text[i : text.index(stop, i)]


def den(s: str) -> int:
    return 10 ** int(s[3:]) if s.startswith("10^") else int(s)


def box_pairs(s: str) -> list[tuple[F, F]]:
    matches = re.findall(
        r"⟨\(?(-?\d+)\s*/\s*(10\^\d+|\d+)\)?,\s*"
        r"\(?(-?\d+)\s*/\s*(10\^\d+|\d+)\)?⟩",
        s,
    )
    return [(F(int(a), den(b)), F(int(c), den(d))) for a, b, c, d in matches]


def box_def(s: str, name: str) -> tuple[F, F]:
    m = re.search(
        rf"def {name} : Box := ⟨\(([-\d]+)/([\d]+)\),\s*"
        rf"\(([-\d]+)/([\d]+)\)⟩",
        s,
    )
    if not m:
        raise ValueError(f"could not parse {name}")
    return F(int(m[1]), int(m[2])), F(int(m[3]), int(m[4]))


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def neg(x):
    return -x[1], -x[0]


def sub(x, y):
    return add(x, neg(y))


def mul(x, y):
    p = [a * b for a in x for b in y]
    return min(p), max(p)


def inv(x):
    return 1 / x[1], 1 / x[0]


def power(x, n):
    out = (F(1), F(1))
    for _ in range(n):
        out = mul(out, x)
    return out


def total(xs):
    lo = F(0)
    hi = F(0)
    for x in xs:
        lo += x[0]
        hi += x[1]
    return lo, hi


def rounded(x, upper: bool, precision: int = 30) -> F:
    grid = 10**precision
    q = x * grid
    floor = q.numerator // q.denominator
    if upper:
        floor += 1
    return F(floor, grid)


def rounded_box(x, precision: int = 30):
    return rounded(x[0], False, precision), rounded(x[1], True, precision)


def lean_q(x: F) -> str:
    return f"{x.numerator} / {x.denominator}"


def lean_box(x) -> str:
    return f"⟨{lean_q(x[0])}, {lean_q(x[1])}⟩"


def main() -> None:
    completed_text = (TASK / "CompletedBoxes48.lean").read_text()
    gamma_text = (TASK / "GammaThirteen.lean").read_text()
    primitive_text = PRIMITIVES.read_text()
    gamma = [F(int(a), den(b)) for a, b in re.findall(
        r"(-?\d+)\s*/\s*(10\^\d+|\d+)",
        section(TASK / "GammaThirteen.lean", "def gammaRealReference13", "def gammaRationalPolynomial13"),
    )]
    gamma0 = gamma[0]
    gamma_normalized = [(x / gamma0, x / gamma0) for x in gamma]
    head = box_pairs(section(TASK / "C3Head48Boxes.lean", "def head48ReferenceBox", "theorem head48_evaluator_check"))
    chart_amp = box_pairs(section(TASK / "CompletedBoxes48.lean", "def chartAmplitudeReferenceTight", "theorem chart_amplitude_tight_contains"))[0]
    log_match = re.search(r"def logReferenceTight : ℚ :=\s*(\d+)\s*/\s*(10\^\d+|\d+)", gamma_text)
    if not log_match:
        raise ValueError("could not parse logReferenceTight")
    log_center = F(int(log_match[1]), den(log_match[2]))
    log_three = (log_center - F(1, 10**44), log_center + F(1, 10**44))
    pi_log = box_def(primitive_text, "piLogReference")
    pi_amp = box_def(primitive_text, "piAmplitudeReference")

    # Original chart jets.  The normalized reciprocal is propagated one order
    # at a time using the already-rounded previous boxes, exactly as the Lean
    # interval recurrence below does.
    chart = []
    for r in range(13):
        point = (F(1), F(1)) if r == 0 else (F(0), F(0))
        chart.append(sub(point, mul(chart_amp,
            mul(power(neg(log_three), r), (F(1, math.factorial(r)), F(1, math.factorial(r)))))))
    chart_table = [(rounded(x[0], False), rounded(x[1], True)) for x in chart]
    chart_scale = chart[0]
    normalized_chart = [(F(1), F(1))]
    for n in range(1, 13):
        s = (F(0), F(0))
        for j in range(n):
            product = rounded_box(mul(normalized_chart[j], chart_table[n-j]))
            s = rounded_box(add(s, product))
        reciprocal_zero = rounded_box(inv(chart_table[0]))
        x = rounded_box(mul(neg(s), reciprocal_zero))
        normalized_chart.append(x)

    pcoef = [F(1)] + [F(0)] * 12
    pcoef[2] = F(-4)
    expcoef = [F((-1) ** e, 2**e * math.factorial(e)) for e in range(13)]

    def base_coeff(n, e):
        if e > n:
            return (F(0), F(0))
        terms = []
        for i in range(n + 1):
            if i + e <= n:
                terms.append(mul((pcoef[i], pcoef[i]),
                    mul((expcoef[e], expcoef[e]), normalized_chart[n-i-e])))
            else:
                terms.append((F(0), F(0)))
        return total(terms)

    def full_coeff(n, e):
        if e > n:
            return (F(0), F(0))
        terms = []
        for j in range(n + 1):
            if e <= j:
                terms.append(mul(base_table[j][e], gamma_normalized[n-j]))
            else:
                terms.append((F(0), F(0)))
        return total(terms)

    base_table = []
    for n in range(13):
        row = []
        for e in range(13):
            x = base_coeff(n, e)
            row.append((rounded(x[0], False, 24), rounded(x[1], True, 24)))
        base_table.append(row)

    completed_coefficient_table = []
    for n in range(13):
        row = []
        for e in range(13):
            x = full_coeff(n, e)
            row.append((rounded(x[0], False, 24), rounded(x[1], True, 24)))
        completed_coefficient_table.append(row)

    outer = []
    for n in range(13):
        x = total(mul(completed_coefficient_table[n][e], power(pi_log, e))
                  for e in range(n+1))
        outer.append((rounded(x[0], False, 24), rounded(x[1], True, 24)))

    completed = []
    for n in range(13):
        completed.append(total(mul(head[k], outer[n-k]) for k in range(n+1)))

    scale_box = mul(mul(mul((F(-1, 8), F(-1, 8)), pi_amp), inv(chart_scale)), (gamma0, gamma0))
    final = []
    for j in range(7):
        x = mul((F((-1) ** j), F((-1) ** j)), mul(scale_box, completed[2*j]))
        final.append((rounded(x[0], False, 24), rounded(x[1], True, 24)))

    print("chartJetBoxTable := ![")
    for x in chart_table:
        print(f"  {lean_box(x)},")
    print("]")
    print("normalizedChartReciprocalBoxTable := ![")
    for x in normalized_chart:
        print(f"  {lean_box(x)},")
    print("]")
    print("normalizedOuterCompletedPolynomialBoxTable := ![")
    for x in outer:
        print(f"  {lean_box(x)},")
    print("]")
    for name, table in (
        ("normalizedOuterBasePolynomialCoefficientBoxTable", base_table),
        ("normalizedOuterCompletedPolynomialCoefficientBoxTable", completed_coefficient_table),
    ):
        print(f"{name} := ![")
        for row in table:
            print("  ![")
            for x in row[:-1]:
                print(f"    {lean_box(x)},")
            print(f"    {lean_box(row[-1])}")
            print("  ],")
        print("]")
    print("nativeEvenFiniteReferenceBoxTable := ![")
    for x in final:
        print(f"  {lean_box(x)},")
    print("]")
    candidates = box_pairs(section(TASK / "IntervalGate.lean", "def candidateCoefficientBall", "def refXBall"))
    print("candidate containment margins:")
    for j, x in enumerate(final):
        lo, hi = x
        c, r = candidates[j]
        margin = min(lo - (c-r), (c+r) - hi)
        print(j, float(margin))


if __name__ == "__main__":
    main()
