#!/usr/bin/env python3
"""Fail-closed axiom audit for the C5 explicit source modulus bound."""

import re
import sys
from pathlib import Path

required = {
    "CarrySigmaObstruction.complexGamma_norm_le_100",
    "CarrySigmaObstruction.complexGamma_norm_le_1000",
    "CarrySigmaObstruction.displacedProductC_norm_le_10pow13_on_ball_39",
    "CarrySigmaObstruction.displacedProductC_norm_le_10pow100_on_ball_39",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_c5_analytic_bounds_axioms.py LEAN_BUILD_LOG")
text = Path(sys.argv[1]).read_text()
if "BUILD_EXIT=0" not in text:
    raise SystemExit("missing successful build marker")

reports = []
names = set()
pattern = re.compile(
    r"'(?P<name>[^']+)' depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"'(?P<free>[^']+)' does not depend on any axioms"
)
for match in pattern.finditer(text):
    if match.group("name"):
        name = match.group("name")
        axioms = {
            item.strip() for item in match.group("axioms").split(",") if item.strip()
        }
    else:
        name = match.group("free")
        axioms = set()
    names.add(name)
    reports.append((name, axioms))

if not required.issubset(names):
    raise SystemExit(f"missing required reports: {sorted(required - names)}")
for name, axioms in reports:
    unexpected = axioms - allowed
    if unexpected:
        raise SystemExit(f"{name}: unexpected axioms {sorted(unexpected)}")
report_count = text.count("depends on axioms:") + text.count("does not depend on any axioms")
if report_count != len(reports):
    raise SystemExit("malformed or truncated axiom report")
if re.search(r"\bsorryAx\b|declaration uses [`']sorry[`']|\berror(?:\([^\n)]*\))?:", text):
    raise SystemExit("Lean reported a placeholder or error")

print(
    f"Accepted {len(reports)} reports; all use only "
    "propext, Classical.choice, Quot.sound."
)
