#!/usr/bin/env python3
"""Fail-closed axiom audit for the 129-node rational interpolation proof."""

import re
import sys
from pathlib import Path

required = {
    "CarrySigmaObstruction.c5InterpolationNode_injOn",
    "CarrySigmaObstruction.c5InterpolationPolynomial_coeff",
    "CarrySigmaObstruction.c5_interpolate_polynomial",
    "CarrySigmaObstruction.c5InterpolationPolynomial_coeff_of_degree_lt",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_c5_interpolation_axioms.py AXIOM_AUDIT_LOG")
text = Path(sys.argv[1]).read_text()
reports = []
for name, axioms, axiom_free in re.findall(
    r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]|'([^']+)' does not depend on any axioms",
    text,
):
    if name:
        actual = {item.strip() for item in axioms.split(",") if item.strip()}
        reports.append((name, actual))
    else:
        reports.append((axiom_free, set()))

names = [name for name, _ in reports]
if not required.issubset(names):
    raise SystemExit(f"Missing required axiom reports: {sorted(required - set(names))}")
for name, axioms in reports:
    unexpected = axioms - allowed
    if unexpected:
        raise SystemExit(f"{name}: unexpected axioms {sorted(unexpected)}")
if text.count("depends on axioms:") + text.count("does not depend on any axioms") != len(reports):
    raise SystemExit("Malformed or truncated axiom report")
if re.search(r"\bsorryAx\b|declaration uses [`']sorry[`']|\berror(?:\([^\n)]*\))?:", text):
    raise SystemExit("Lean reported a placeholder or error")

print(f"Accepted {len(reports)} reports; all use only propext, Classical.choice, Quot.sound.")
