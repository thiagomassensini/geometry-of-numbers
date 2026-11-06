#!/usr/bin/env python3
"""Fail-closed axiom audit for the public C3 parity results."""

import re
import sys
from pathlib import Path

expected = {
    "CarrySigmaObstruction.sigmaMatrix_negative_direction_of_negative_pade_minor",
    "CarrySigmaObstruction.sigmaMatrix_negative_directions_of_window",
    "CarrySigmaObstruction.exists_even_sigma_negative_directions_from_pade",
    "CarrySigmaObstruction.exists_odd_sigma_negative_directions_from_pade",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_c3_axioms.py BUILD_LOG")
text = Path(sys.argv[1]).read_text()
reports = re.findall(
    r"^'([^'\n]+)' depends on axioms: \[(.*?)\]$", text, re.MULTILINE | re.DOTALL
)
names = [name for name, _ in reports]
if set(names) != expected or len(names) != len(expected):
    raise SystemExit(f"Expected exactly {sorted(expected)}, received {names}")
for name, axioms in reports:
    actual = [axiom.strip() for axiom in axioms.replace("\n", " ").split(",")]
    if set(actual) != allowed or len(actual) != len(allowed):
        raise SystemExit(f"{name}: expected only the three standard axioms, received {actual}")
if text.count("depends on axioms:") != len(reports):
    raise SystemExit("Malformed or truncated axiom report")
if re.search(r"\bsorryAx\b|declaration uses [`']sorry[`']|\berror(?:\([^\n)]*\))?:", text):
    raise SystemExit("Lean reported a placeholder or error")
print(f"Accepted all {len(expected)} C3 reports: propext, Classical.choice, Quot.sound only.")
