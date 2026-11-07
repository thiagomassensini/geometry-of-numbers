#!/usr/bin/env python3
"""Flatten the four exact Lean zeta-box logs into a node-indexed CSV."""
from __future__ import annotations

import csv
import re
from pathlib import Path

ROOT = Path(__file__).parent
OUTPUT = ROOT / "c5-centered-all-a-zeta-boxes.csv"
SOURCES = (
    ("2/5", "c5-centered-all-a-0400-probe-retry2.log"),
    ("901/2000", "c5-centered-all-a-4505-probe-retry1.log"),
    ("1099/2000", "c5-centered-all-a-5495-probe-retry1.log"),
    ("3/5", "c5-centered-all-a-0600-probe-retry1.log"),
)
RATIONAL = re.compile(r"-?\d+(?:/\d+)?\Z")

with OUTPUT.open("w", newline="") as out:
    writer = csv.writer(out, lineterminator="\n")
    writer.writerow(("a", "j", "re_lo", "re_hi", "im_lo", "im_hi", "source_log"))
    total = 0
    for a, filename in SOURCES:
        path = ROOT / filename
        rows = []
        for line in path.read_text().splitlines():
            match = re.fullmatch(r"(\d+), (.*)", line)
            if match is None:
                continue
            values = match.group(2).split(", ")
            if len(values) != 4 or not all(RATIONAL.fullmatch(value) for value in values):
                raise ValueError(f"malformed exact endpoint in {filename}: {line[:200]}")
            rows.append((int(match.group(1)), *values))
        if [row[0] for row in rows] != list(range(129)):
            raise ValueError(f"{filename}: expected indices 0..128, got {len(rows)} rows")
        for j, *bounds in rows:
            writer.writerow((a, j, *bounds, filename))
        total += len(rows)
    if total != 4 * 129:
        raise ValueError(f"expected 516 rows, got {total}")

print(f"wrote {total} exact node boxes to {OUTPUT.name}")
