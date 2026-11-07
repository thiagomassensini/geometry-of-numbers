#!/usr/bin/env python3
"""Fail-closed axiom audit for the rational C5 zeta node evaluator."""

import re
import sys
from pathlib import Path

required = {
    "CarrySigmaObstruction.c5RatComplexToComplex_pow",
    "CarrySigmaObstruction.c5RatPochhammer_toComplex",
    "CarrySigmaObstruction.c5RatCorrectionTerm_toComplex",
    "CarrySigmaObstruction.c5RatCorrectionSum_toComplex",
    "CarrySigmaObstruction.c5RatScale_toComplex",
    "CarrySigmaObstruction.c5_emZetaHighRHS_factor",
    "CarrySigmaObstruction.c5ComplexIntervalRangeSum_contains",
    "CarrySigmaObstruction.c5RationalZetaHeadBox_contains",
    "CarrySigmaObstruction.c5RationalZetaBasePowerBox_contains",
    "CarrySigmaObstruction.c5RationalZetaNodeBox_contains",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_c5_rational_node_eval_axioms.py AXIOM_AUDIT_LOG")

text = Path(sys.argv[1]).read_text()
reports = []
for match in re.finditer(
    r"'(?P<name>[^']+)' depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"'(?P<free>[^']+)' does not depend on any axioms",
    text,
):
    if match.group("name"):
        name = match.group("name")
        axioms = {item.strip() for item in match.group("axioms").split(",") if item.strip()}
    else:
        name = match.group("free")
        axioms = set()
    reports.append((name, axioms))

if text.count("depends on axioms:") + text.count("does not depend on any axioms") != len(reports):
    raise SystemExit("malformed or truncated axiom report")
if re.search(r"\bsorryAx\b|declaration uses [`']sorry[`']|\berror(?:\([^\n)]*\))?:", text):
    raise SystemExit("Lean reported a placeholder or error")
names = {name for name, _ in reports}
if not required.issubset(names):
    raise SystemExit(f"missing required axiom reports: {sorted(required - names)}")
for name, axioms in reports:
    unexpected = axioms - allowed
    if unexpected:
        raise SystemExit(f"{name}: unexpected axioms {sorted(unexpected)}")

print(f"Accepted {len(reports)} reports; only standard classical/propositional axioms occur.")
