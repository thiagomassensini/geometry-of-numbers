#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
from pathlib import Path

if len(sys.argv) != 3:
    raise SystemExit("usage: check-data-table.py PROBE_LOG DATA_LEAN")

probe = Path(sys.argv[1]).read_text()
source = Path(sys.argv[2]).read_text()
probe_values = re.findall(r"^(\d+): (-?\d+(?:/\d+)?)$", probe, re.MULTILINE)
if len(probe_values) != 601:
    raise SystemExit(f"expected 601 probe values, got {len(probe_values)}")
for i, (index, _) in enumerate(probe_values):
    if int(index) != i:
        raise SystemExit(f"probe index {index} at row {i}")
data_defs = re.findall(
    r"def c5BernoulliPrimeDataPrefix\d+ : Array ℚ :=(.*?)(?=\n\ndef c5BernoulliPrimeDataPrefix|\n\ndef c5BernoulliPrimeData601)",
    source,
    re.DOTALL,
)
data_values: list[str] = []
for body in data_defs:
    literals = re.findall(r"#\[(.*?)\]", body, re.DOTALL)
    if len(literals) != 1:
        raise SystemExit("expected exactly one data chunk in each prefix definition")
    chunk = re.findall(r"-?\d+(?:/\d+)?", literals[0])
    data_values.extend(chunk)
if len(data_values) != 601:
    raise SystemExit(f"expected 601 literal coefficients, got {len(data_values)}")
for i, ((_, probe_value), data_value) in enumerate(zip(probe_values, data_values)):
    if probe_value != data_value:
        raise SystemExit(f"coefficient {i} differs: probe={probe_value}, data={data_value}")
print("DATA_TABLE_CHECK=PASS")
print("COEFFICIENTS=601")
