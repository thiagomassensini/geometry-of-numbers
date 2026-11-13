#!/usr/bin/env python3
"""Regenerate tight original-source input and M=80 jet caches.

The low-address tables mirror the proved rationalLogBox/expBox evaluators.
The jet table is checked by Lean against the integer-grid source evaluator.
All arithmetic and rounding are exact fractions.
"""
from __future__ import annotations

import math
import re
import sys
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = Path("/home/thlinux/geometry-of-numbers")
OLD_RESEARCH = HERE.parents[3] / "worktrees/pade-sem-divisao-20261112/research"
PRIMITIVES = ROOT / "research/c3-fourteenth-tail/SamplePrimitiveBoxes.lean"
HIGH_AMPLITUDES = HERE / "HighSampleAmplitude17.lean"
HIGH_LOGS = HERE / "HighLogTable.lean"
BOUNDARY = OLD_RESEARCH / "c3-cofactor-chiral-certification/C3Boundary48Stencil.lean"
DEN = 10**30

Interval = tuple[F, F]
GridBox = tuple[int, int]


def read_table(path: Path, name: str) -> list[Interval]:
    source = path.read_text()
    start = source.index(f"def {name}")
    body = source[start:]
    body = body[body.index("![") + 2:]
    body = body[:body.index("]")]
    pat = re.compile(
        r"⟨\s*\(?(-?\d+)\s*/\s*(\d+)\)?\s*,\s*"
        r"\(?(-?\d+)\s*/\s*(\d+)\)?\s*⟩"
    )
    values = [(F(int(a), int(b)), F(int(c), int(d)))
              for a, b, c, d in pat.findall(body)]
    if not values:
        raise ValueError(f"no interval table parsed for {name} in {path}")
    return values


def grid_endpoint(x: F) -> int:
    y = x * DEN
    return y.numerator // y.denominator


def grid_of_box(a: Interval) -> GridBox:
    return grid_endpoint(a[0]), grid_endpoint(a[1]) + 1


def gpoint(z: int) -> GridBox:
    return z * DEN, z * DEN


def gadd(a: GridBox, b: GridBox) -> GridBox:
    return a[0] + b[0], a[1] + b[1] + 1


def gneg(a: GridBox) -> GridBox:
    return -a[1], -a[0]


def gsub(a: GridBox, b: GridBox) -> GridBox:
    return a[0] - b[1], a[1] - b[0] + 1


def gmul(a: GridBox, b: GridBox) -> GridBox:
    products = (a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1])
    floors = [x // DEN for x in products]
    return min(floors), max(floors) + 1


def gscale(a: GridBox, q: F) -> GridBox:
    products = (F(a[0], DEN)*q, F(a[1], DEN)*q)
    floors = [grid_endpoint(x) for x in products]
    return min(floors), max(floors) + 1


def gpow(a: GridBox, n: int) -> GridBox:
    out = gpoint(1)
    for _ in range(n):
        out = gmul(out, a)
    return out


def exact_mul(a: Interval, b: Interval) -> Interval:
    products = [x * y for x in a for y in b]
    return min(products), max(products)


def exact_power(a: Interval, n: int) -> Interval:
    out = (F(1), F(1))
    for _ in range(n):
        out = exact_mul(out, a)
    return out


def gsample(amplitude: Interval, logarithm: Interval, r: int) -> GridBox:
    amp_grid = grid_of_box(amplitude)
    log_grid = gneg(grid_of_box(logarithm))
    power = gpoint(1)
    for _ in range(r):
        power = gmul(power, log_grid)
    return gscale(gmul(amp_grid, power), F(1, math.factorial(r)))


def qbox(q: F) -> GridBox:
    return grid_of_box((q, q))


def rounded(a: Interval) -> Interval:
    return F(grid_endpoint(a[0]), DEN), F(grid_endpoint(a[1]) + 1, DEN)


def badd(a: Interval, b: Interval) -> Interval:
    return rounded((a[0] + b[0], a[1] + b[1]))


def bmul(a: Interval, b: Interval) -> Interval:
    return rounded(exact_mul(a, b))


def unit_log_box(a: F) -> Interval:
    value = -sum((1-a) ** (j+1) / F(j+1) for j in range(128))
    return rounded((value - F(1, 10**35), value + F(1, 10**35)))


def tight_log_box(n: int) -> Interval:
    p = n.bit_length()
    half = unit_log_box(F(1, 2))
    scaled = unit_log_box(F(n, 2**p))
    return badd(bmul((F(p), F(p)), (-half[1], -half[0])), scaled)


def tight_exp_box(a: Interval) -> Interval:
    total: Interval = (F(0), F(0))
    power: Interval = (F(1), F(1))
    for k in range(64):
        total = badd(total, bmul(power, (F(1, math.factorial(k)),) * 2))
        power = bmul(power, a)
    return total[0] - F(1, DEN), total[1] + F(1, DEN)


def interval_lean(name: str, values: list[Interval], size: int) -> str:
    rows = [f"  ⟨({lo.numerator}/{lo.denominator}), ({hi.numerator}/{hi.denominator})⟩"
            for lo, hi in values]
    return f"def {name} : Fin {size} → Box := ![\n" + ",\n".join(rows) + "\n]\n"


def head_box(samples: list[GridBox], r: int, weights: list[F]) -> GridBox:
    cells: list[GridBox] = []
    for m in range(80):
        x, y, z = samples[3*m+1], samples[3*m+2], samples[3*m+3]
        cells.append(gadd(gsub(x, gmul(gpoint(2), y)), z))
    cell_sum: GridBox = (0, 0)
    for cell in cells:
        cell_sum = gadd(cell_sum, cell)
    boundary_sum: GridBox = (0, 0)
    for k, weight in enumerate(weights):
        term = gmul(qbox(weight), samples[241+k])
        boundary_sum = gadd(boundary_sum, term)
    constant = gpoint(1 if r == 0 else 0)
    return gadd(gadd(constant, cell_sum), boundary_sum)


def lean_table(name: str, values: list[GridBox]) -> str:
    rows = [f"  ⟨{lo}, {hi}⟩" for lo, hi in values]
    return f"def {name} : Fin 265 → GridBox := ![\n" + ",\n".join(rows) + "\n]\n"


def generate() -> tuple[str, str]:
    low_logs = [tight_log_box(n) for n in range(1, 206)]
    low_amps = [tight_exp_box(bmul((F(-1, 2), F(-1, 2)), log))
                for log in low_logs]
    high_amps = read_table(HIGH_AMPLITUDES, "tightHighSampleAmplitudeReference")
    high_logs = read_table(HIGH_LOGS, "tightHighSampleLogBox")
    if (len(low_logs), len(low_amps), len(high_logs), len(high_amps)) != (205, 205, 60, 60):
        raise AssertionError("unexpected source table sizes")
    logs = low_logs + high_logs
    amps = low_amps + high_amps
    if len(logs) != 265:
        raise AssertionError("M=80 source must expose 265 sample addresses")

    weight_body = BOUNDARY.read_text().split("def boundary48Weight", 1)[1].split("] k", 1)[0]
    weight_tokens = re.findall(r"(-?\d+)(?::ℚ)?\)?\s*/\s*(\d+)(?:\^(\d+))?", weight_body)
    weights = [F(int(a), int(b) ** int(p or 1)) for a, b, p in weight_tokens]
    if len(weights) != 24:
        raise AssertionError(f"expected 24 boundary weights, found {len(weights)}")

    jets = [[gsample(a, l, r) for a, l in zip(amps, logs)] for r in range(17)]
    heads = [head_box(jets[r], r, weights) for r in range(17)]
    inputs = (
        "import HighSampleAmplitude17\n\nnamespace C3ShiftedFourth\n\n"
        "open CarryC3Boxes\n\nnoncomputable section\nset_option maxRecDepth 30000\n"
        "/-- Exact low-address outputs of the original `rationalLogBox` and `expBox` evaluators. -/\n"
        + interval_lean("tightLowSampleLogReference17", low_logs, 205) + "\n"
        + interval_lean("tightLowSampleAmplitudeReference17", low_amps, 205)
        + "\nend\nend C3ShiftedFourth\n"
    )
    jets = (
        "import GridArithmetic17\n\nnamespace C3ShiftedFourth\n\n"
        "noncomputable section\nset_option maxRecDepth 30000\n"
        "/-- Generated from the 205 original primitive boxes and the 60 M=80 `expBox`/log boxes. -/\n"
        + "\n".join(
            lean_table(f"gridM80SampleJet{r}Reference17", jets[r])
            for r in range(17)
        ) + "\n"
        + "\n".join(
            f"def gridM80Head{r}Reference17 : GridBox := ⟨{heads[r][0]}, {heads[r][1]}⟩"
            for r in range(17)
        ) + "\n\n"
        + "end\nend C3ShiftedFourth\n"
    )
    return inputs, jets


def main() -> None:
    input_path = HERE / "TightInputTable17.lean"
    output = HERE / "GridJetTable17.lean"
    inputs, content = generate()
    if "--check" in sys.argv:
        if not input_path.exists() or input_path.read_text() != inputs:
            raise SystemExit("TightInputTable17.lean differs from its exact-rational generator")
        if not output.exists() or output.read_text() != content:
            raise SystemExit("GridJetTable17.lean differs from its exact-rational generator")
        print("PASS: tight input tables and all 4,505 integer-grid sample jets regenerate exactly")
    else:
        input_path.write_text(inputs)
        output.write_text(content)
        print(f"wrote {input_path} ({len(inputs)} bytes)")
        print(f"wrote {output} ({len(content)} bytes)")


if __name__ == "__main__":
    main()
