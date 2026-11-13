#!/usr/bin/env python3
"""Exact-rational preflight for C3 head, Gamma ledger, and size-4 cofactor gate.

This mirrors the already-proved rational Box operations in the C3/48 sources.
It is a diagnostic for selecting certificate tables. The corresponding Lean
containments remain required before any sign can be claimed for the source.
"""
from __future__ import annotations

import re
from fractions import Fraction as F
from pathlib import Path

from mpmath import mp

from diagnose_c3_shifted_fourth import (
    ORDER, DOUBLE_STENCIL, c3_head_jets, decimal_fraction,
    exact_cofactor_gate, fixed_direction, rational_center, source_coefficients,
)


ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "research/c3-fourteenth-tail/SamplePrimitiveBoxes.lean"
PRIMITIVES = ROOT / "research/c3-fourteenth-tail/CompletionPrimitiveBoxes.lean"
HEAD_BOXES = ROOT / "research/c3-cofactor-chiral-certification/C3Head48Boxes.lean"
CHIRAL_BOXES = ROOT / "research/c3-cofactor-chiral-certification/CompletedBoxes48.lean"
GAMMA = ROOT / "research/c3-cofactor-chiral-certification/GammaThirteen.lean"
DEN = 10**30

Interval = tuple[F, F]


def box(lo: F, hi: F | None = None) -> Interval:
    return lo, lo if hi is None else hi


def round_box(a: Interval) -> Interval:
    lo_num = (a[0] * DEN).numerator // (a[0] * DEN).denominator
    hi_scaled = a[1] * DEN
    hi_num = hi_scaled.numerator // hi_scaled.denominator + 1
    return F(lo_num, DEN), F(hi_num, DEN)


def add(a: Interval, b: Interval) -> Interval:
    return a[0] + b[0], a[1] + b[1]


def neg(a: Interval) -> Interval:
    return -a[1], -a[0]


def sub(a: Interval, b: Interval) -> Interval:
    return add(a, neg(b))


def mul(a: Interval, b: Interval) -> Interval:
    vals = [x * y for x in a for y in b]
    return min(vals), max(vals)


def badd(a: Interval, b: Interval) -> Interval:
    return round_box(add(a, b))


def bsub(a: Interval, b: Interval) -> Interval:
    return round_box(sub(a, b))


def bmul(a: Interval, b: Interval) -> Interval:
    return round_box(mul(a, b))


def power(a: Interval, n: int, rounded: bool = False) -> Interval:
    result = box(F(1))
    for _ in range(n):
        result = bmul(result, a) if rounded else mul(result, a)
    return result


def sum_exact(values: list[Interval]) -> Interval:
    return sum((v[0] for v in values), F(0)), sum((v[1] for v in values), F(0))


def pairs_in_definition(path: Path, name: str) -> list[Interval]:
    source = path.read_text()
    start = source.index(f"def {name}")
    end_candidates = [source.find("\ndef ", start + 4), source.find("\ntheorem ", start), source.find("\nend ", start)]
    end_candidates = [e for e in end_candidates if e >= 0]
    end = min(end_candidates) if end_candidates else len(source)
    chunk = source[start:end]
    regex = re.compile(r"⟨\(?(-?\d+)\s*/\s*(\d+)\)?,\s*\(?(-?\d+)\s*/\s*(\d+)\)?⟩")
    return [(F(int(a), int(b)), F(int(c), int(d))) for a, b, c, d in regex.findall(chunk)]


def pair_definition(path: Path, name: str) -> Interval:
    source = path.read_text()
    start = source.index(f"def {name}")
    end_candidates = [source.find("\ndef ", start + 4), source.find("\ntheorem ", start), source.find("\nend ", start)]
    end_candidates = [e for e in end_candidates if e >= 0]
    end = min(end_candidates) if end_candidates else len(source)
    body = source[start:end]
    body = body[body.index(":=") + 2:]
    values = re.findall(r"\(?(-?\d+)\s*/\s*(10\^\d+|\d+)\)?", body)
    if len(values) != 2:
        raise ValueError(f"could not parse rational interval {name}: {body[:200]}")
    def parse(pair):
        den = 10 ** int(pair[1][3:]) if pair[1].startswith("10^") else int(pair[1])
        return F(int(pair[0]), den)
    return parse(values[0]), parse(values[1])


def point_definition(path: Path, name: str) -> F:
    source = path.read_text()
    start = source.index(f"def {name}")
    end_candidates = [source.find("\ndef ", start + 4), source.find("\ntheorem ", start), source.find("\nend ", start)]
    end_candidates = [e for e in end_candidates if e >= 0]
    end = min(end_candidates) if end_candidates else len(source)
    body = source[start:end]
    match = re.search(r":=\s*\(?(-?\d+)\s*/\s*(10\^\d+|\d+)\)?", body)
    if not match:
        raise ValueError(f"could not parse rational point {name}: {body[:200]}")
    denominator = 10 ** int(match.group(2)[3:]) if match.group(2).startswith("10^") else int(match.group(2))
    return F(int(match.group(1)), denominator)


def factorial_box(n: int) -> Interval:
    return box(F(1, __import__("math").factorial(n)))


def parse_source_boxes():
    logs = pairs_in_definition(SOURCE, "sampleLogReference")
    amplitudes = pairs_in_definition(SOURCE, "sampleAmplitudeReference")
    head_table = pairs_in_definition(HEAD_BOXES, "head48ReferenceBox")
    if (len(logs), len(amplitudes), len(head_table)) != (205, 205, 13):
        raise AssertionError(f"unexpected parsed table sizes {len(logs)}, {len(amplitudes)}, {len(head_table)}")
    return logs, amplitudes, head_table


def sample_box(n: int, r: int, logs: list[Interval], amplitudes: list[Interval]) -> Interval:
    # FiniteCoefficientBoxes.sampleJetBox: amp * ((-log)^r * 1/r!),
    # with bmul/bpow rounding after each operation.
    return bmul(amplitudes[n], bmul(power(neg(logs[n]), r, rounded=True), factorial_box(r)))


def raw_head_box(r: int, logs: list[Interval], amplitudes: list[Interval]) -> Interval:
    cells = []
    for m in range(48):
        x = sample_box(3 * m + 1, r, logs, amplitudes)
        y = sample_box(3 * m + 2, r, logs, amplitudes)
        z = sample_box(3 * m + 3, r, logs, amplitudes)
        cells.append(badd(bsub(x, bmul(box(F(2)), y)), z))
    cell_sum = box(F(0))
    for term in cells:
        cell_sum = badd(cell_sum, term)
    boundary_sum = box(F(0))
    for k, stencil in enumerate(DOUBLE_STENCIL):
        weight = F(stencil, 729**2)
        term = bmul(box(weight), sample_box(145 + k, r, logs, amplitudes))
        boundary_sum = badd(boundary_sum, term)
    return badd(badd(box(F(1) if r == 0 else F(0)), cell_sum), boundary_sum)


def chart_jets() -> list[Interval]:
    amp = pair_definition(CHIRAL_BOXES, "chartAmplitudeReferenceTight")
    log_center = point_definition(GAMMA, "logReferenceTight")
    log3 = (log_center - F(1, 10**44), log_center + F(1, 10**44))
    out = []
    for r in range(ORDER + 1):
        monomial = mul(power(neg(log3), r), factorial_box(r))
        out.append(sub(box(F(1) if r == 0 else F(0)), mul(amp, monomial)))
    return out


def reciprocal_jets(c: list[Interval]) -> list[Interval]:
    out = [box(1 / c[0][1], 1 / c[0][0])]
    for n in range(1, ORDER + 1):
        s = sum_exact([mul(out[j], c[n - j]) for j in range(n)])
        out.append(mul(neg(s), out[0]))
    return out


def convolution(a: list[Interval], b: list[Interval]) -> list[Interval]:
    return [sum_exact([mul(a[j], b[n - j]) for j in range(n + 1)]) for n in range(ORDER + 1)]


def exact_left_jet_boxes():
    logs, amplitudes, head_table = parse_source_boxes()
    head = head_table + [raw_head_box(r, logs, amplitudes) for r in range(13, ORDER + 1)]
    pi_amp = pair_definition(PRIMITIVES, "piAmplitudeReference")
    pi_log = pair_definition(PRIMITIVES, "piLogReference")
    exponential = []
    polyarg = mul(box(F(-1, 2)), pi_log)
    for r in range(ORDER + 1):
        exponential.append(mul(pi_amp, mul(power(polyarg, r), factorial_box(r))))
    reciprocal = reciprocal_jets(chart_jets())
    polynomial = [box(F(-1, 8) if r == 0 else F(1, 2) if r == 2 else F(0)) for r in range(ORDER + 1)]
    return convolution(convolution(convolution(polynomial, exponential), reciprocal), head), head


def main() -> None:
    mp.dps = 125
    left, head = exact_left_jet_boxes()
    gamma_jets = mp.taylor(lambda w: mp.gamma((mp.mpf(1) / 4) + mp.j * w / 2), 0, ORDER)
    gamma_real = [mp.re(gamma_jets[r] / (mp.j**r)) for r in range(ORDER + 1)]
    coefficients = source_coefficients(80)
    direction = fixed_direction(coefficients)
    centers = [rational_center(x) for x in coefficients]

    print("Exact rational original-head and left-jet interval widths")
    print("(sample/head operations reproduce Box grid rounding; reciprocal/convolutions use exact Box arithmetic)")
    for r in (12, 13, 14, 15, 16):
        print(f"  head jet {r}: width={decimal_fraction(head[r][1]-head[r][0], 20)}")
        print(f"  left jet {r}: width={decimal_fraction(left[r][1]-left[r][0], 20)}")

    source_boxes = []
    for j in range(9):
        n = 2 * j
        gamma_terms = []
        for k in range(n + 1):
            g_center = rational_center(gamma_real[n-k])
            g_radius = F(2 * 4**(n-k), 10**34) + F(1, 10**55)
            gamma_terms.append(mul(left[k], (g_center-g_radius, g_center+g_radius)))
        completed = sum_exact(gamma_terms)
        if j % 2:
            completed = neg(completed)
        tail = F(96 * __import__("math").factorial(26) * 4**n, 729**2 * 239**25)
        source_boxes.append((completed[0] - tail, completed[1] + tail))

    candidate_radii = []
    print("C3/80 candidate coefficient enclosures from finite head, Gamma ledger, and original tail")
    for j, (interval, center) in enumerate(zip(source_boxes, centers)):
        radius = max(center - interval[0], interval[1] - center)
        candidate_radii.append(radius)
        print(f"  c{j}: [{decimal_fraction(interval[0], 34)}, {decimal_fraction(interval[1], 34)}], radius about {decimal_fraction(radius, 18)}")

    constant, variation, lower, terms, det_a = exact_cofactor_gate(centers, candidate_radii, direction)
    print(f"source-box exact gate terms={terms}")
    print(f"source-box gate center={decimal_fraction(constant, 42)}")
    print(f"source-box gate variation={decimal_fraction(variation, 42)}")
    print(f"source-box exact lower={decimal_fraction(lower, 42)}")
    print("classification:", "candidate box gate passes" if lower > 0 else "candidate box gate fails")
    print("Lean must still prove the finite head boxes, Gamma error, and C3/48 tail inclusion.")


if __name__ == "__main__":
    main()
