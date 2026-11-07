#!/usr/bin/env python3
"""Fail-closed axiom audit for the certified 512-term log2 interval."""

import re
import sys
from pathlib import Path

required = {
    "CarrySigmaObstruction.c5LogSum512_pos_eq",
    "CarrySigmaObstruction.c5LogSum512_neg_eq",
    "CarrySigmaObstruction.c5CenteredLog2I_512_eq_export",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_c5_log2_axioms.py AXIOM_AUDIT_LOG")
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
if re.search(r"\bsorryAx\b|declaration uses [`']sorry[`']|\berror(?:\([^\n)]*\))?:", text):
    raise SystemExit("Lean reported a placeholder or error")

print("Accepted all three reports; only propext, Classical.choice, and Quot.sound occur.")
