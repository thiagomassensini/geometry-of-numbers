#!/usr/bin/env python3
"""Emit exact Lean rational-ball constants from the archived C5 JSON boxes."""

from fractions import Fraction
import json
from pathlib import Path


mission = Path(__file__).resolve().parent
evidence = mission / "evidence" / "interval-certificate"
target = mission.parent / "SigmaFiniteRationalIntervalBoxes.lean"


def rat(value: Fraction) -> str:
    return f"(({value.numerator} : ℚ) / {value.denominator})"


def read_balls(filename: str) -> list[tuple[Fraction, Fraction]]:
    document = json.loads((evidence / filename).read_text())
    intervals = document["source_c_exact_rational_decimal_intervals"]
    result = []
    for lower_text, upper_text in intervals:
        lower = Fraction(lower_text)
        upper = Fraction(upper_text)
        if lower > upper:
            raise ValueError(f"reversed interval in {filename}: {lower_text}, {upper_text}")
        result.append(((lower + upper) / 2, (upper - lower) / 2))
    return result


def emit_function(name: str, balls: list[tuple[Fraction, Fraction]]) -> list[str]:
    lines = [f"def {name} : ℕ → SigmaRatBall"]
    for index, (center, radius) in enumerate(balls):
        lines.append(f"  | {index} => ({rat(center)}, {rat(radius)})")
    lines.append("  | _ => sigmaRatBallConst 0")
    return lines


left = read_balls("sign1024_stirling.json")
right = read_balls("sign512_d01_L12.json")
if len(left) != 15 or len(right) != 13:
    raise ValueError(f"unexpected coefficient box lengths: {len(left)}, {len(right)}")

lines = [
    "import SigmaFiniteRationalIntervals",
    "",
    "/-!",
    "# Exact C5 coefficient boxes",
    "",
    "Generated from the `source_c_exact_rational_decimal_intervals` entries of the two",
    "archived JSON certificates. Each pair is the exact rational midpoint and radius.",
    "This file records the box data; it does not assert source-coefficient inclusion.",
    "-/",
    "",
    "namespace CarrySigmaObstruction",
    "",
    *emit_function("sigmaC00495CoefficientBall", left),
    "",
    *emit_function("sigmaC01CoefficientBall", right),
    "",
    "end CarrySigmaObstruction",
    "",
]
target.write_text("\n".join(lines))
