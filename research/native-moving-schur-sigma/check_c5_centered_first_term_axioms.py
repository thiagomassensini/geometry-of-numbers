#!/usr/bin/env python3
"""Fail-closed axiom audit for the first centered C5 Dirichlet term."""

import re
import sys
from pathlib import Path

required = {
    "CarrySigmaObstruction.c5CenteredDirichletTermBox_one_eq_generic",
    "CarrySigmaObstruction.c5CenteredDirichletTermBox_one_fixed",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_c5_centered_first_term_axioms.py AXIOM_AUDIT_LOG")
text = Path(sys.argv[1]).read_text()
reports = []
for name, axioms, axiom_free in re.findall(
    r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]|'([^']+)' does not depend on any axioms",
    text,
):
    if name:
        reports.append((name, {item.strip() for item in axioms.split(",") if item.strip()}))
    else:
        reports.append((axiom_free, set()))

names = [name for name, _ in reports]
if set(names) != required or len(names) != len(required):
    raise SystemExit(f"Expected exactly {sorted(required)}, received {names}")
for name, axioms in reports:
    unexpected = axioms - allowed
    if unexpected:
        raise SystemExit(f"{name}: unexpected axioms {sorted(unexpected)}")
if text.count("depends on axioms:") + text.count("does not depend on any axioms") != len(reports):
    raise SystemExit("Malformed or truncated axiom report")
if re.search(r"\bsorryAx\b|declaration uses [`']sorry[`']|\badmit\b|error(?:\([^\n)]*\))?:", text):
    raise SystemExit("Lean reported a placeholder or error")

print("Accepted both reports; only propext, Classical.choice, and Quot.sound occur.")
