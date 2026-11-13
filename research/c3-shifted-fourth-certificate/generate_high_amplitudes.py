#!/usr/bin/env python3
"""Reproduce/check the exact rational amplitude table used by Lean.

The script mirrors the rational Box arithmetic in ElementaryBoxes.lean for the
60 extra sample log boxes. Lean independently checks every generated value by
recomputing expBox and proving the finite subset statement.
"""
from __future__ import annotations

import math
import re
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCALE = 10**30


def parse_fraction(text: str) -> F:
    numerator, denominator = text.strip().split("/")
    return F(int(numerator.strip()), int(denominator.strip()))


def rounded(box: tuple[F, F]) -> tuple[F, F]:
    lo, hi = box
    lo_scaled, hi_scaled = lo * SCALE, hi * SCALE
    return F(lo_scaled.numerator // lo_scaled.denominator, SCALE), F(
        hi_scaled.numerator // hi_scaled.denominator + 1, SCALE
    )


def bmul(a: tuple[F, F], b: tuple[F, F]) -> tuple[F, F]:
    products = [x * y for x in a for y in b]
    return rounded((min(products), max(products)))


def exp_box(a: tuple[F, F]) -> tuple[F, F]:
    total = (F(0), F(0))
    power = (F(1), F(1))
    for k in range(64):
        term = bmul(power, (F(1, math.factorial(k)),) * 2)
        total = rounded((total[0] + term[0], total[1] + term[1]))
        power = bmul(power, a)
    return total[0] - F(1, SCALE), total[1] + F(1, SCALE)


def main() -> None:
    source = (HERE / "HighLogTable.lean").read_text()
    table = (HERE / "HighSampleAmplitude17.lean").read_text()
    body = source.split("def tightHighSampleLogBox : Fin 60 → Box := ![", 1)[1]
    body = body.split("\n]\n", 1)[0]
    log_pairs = re.findall(r"⟨\s*([^,]+),\s*([^⟩]+)\s*⟩", body)
    if len(log_pairs) != 60:
        raise SystemExit(f"expected 60 high log boxes, found {len(log_pairs)}")

    expected = []
    for lo_text, hi_text in log_pairs:
        log_box = (parse_fraction(lo_text), parse_fraction(hi_text))
        scaled_log = bmul((F(-1, 2), F(-1, 2)), log_box)
        expected.append(exp_box(scaled_log))

    amp_body = table.split(
        "def tightHighSampleAmplitudeReference : Fin 60 → Box := ![", 1
    )[1].split("\n]", 1)[0]
    found = [
        (F(int(a), int(b)), F(int(c), int(d)))
        for a, b, c, d in re.findall(
            r"⟨\((-?\d+)/(\d+)\),\s*\((-?\d+)/(\d+)\)⟩", amp_body
        )
    ]
    if found != expected:
        raise SystemExit("Lean amplitude table differs from exact rational regeneration")
    print("PASS: all 60 Lean amplitude entries match the exact rational expBox evaluator")


if __name__ == "__main__":
    main()
