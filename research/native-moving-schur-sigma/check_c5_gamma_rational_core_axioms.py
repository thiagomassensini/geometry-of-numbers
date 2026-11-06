#!/usr/bin/env python3
"""Fail-closed audit for the rational-core Gamma enclosure bridge."""

import re
import sys
from pathlib import Path

required = {
    "SigmaC5Gamma.ratComplexToComplex_mul",
    "SigmaC5Gamma.ratComplexToComplex_inv",
    "SigmaC5Gamma.gammaFinite_eq_rationalCore",
    "SigmaC5Gamma.gammaFiniteRationalCoreInterval_contains",
    "SigmaC5Gamma.gammaFiniteInterval_contains",
    "SigmaC5Gamma.gamma3072Interval_contains",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}
pattern = re.compile(
    r"'(?P<name>[^']+)' depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"'(?P<free>[^']+)' does not depend on any axioms"
)

if len(sys.argv) != 3:
    raise SystemExit("usage: check_c5_gamma_rational_core_axioms.py SOURCE_LOG AUDIT_LOG")

all_reports = []
for filename in sys.argv[1:]:
    text = Path(filename).read_text()
    if "BUILD_EXIT=0" not in text or re.search(r"\bBUILD_EXIT=(?!0\b)", text):
        raise SystemExit(f"{filename}: missing successful build marker")
    reports = []
    for match in pattern.finditer(text):
        if match.group("name"):
            name = match.group("name")
            axioms = {
                item.strip() for item in match.group("axioms").split(",") if item.strip()
            }
        else:
            name = match.group("free")
            axioms = set()
        reports.append((name, axioms))
    report_count = text.count("depends on axioms:") + text.count(
        "does not depend on any axioms"
    )
    if report_count != len(reports):
        raise SystemExit(f"{filename}: malformed or truncated axiom report")
    if re.search(r"\bsorryAx\b|declaration uses [`']sorry[`']|\berror(?:\([^\n)]*\))?:", text):
        raise SystemExit(f"{filename}: Lean reported a placeholder or error")
    for name, axioms in reports:
        unexpected = axioms - allowed
        if unexpected:
            raise SystemExit(f"{name}: unexpected axioms {sorted(unexpected)}")
    all_reports.extend(reports)

names = {name for name, _ in all_reports}
if not required.issubset(names):
    raise SystemExit(f"missing required axiom reports: {sorted(required - names)}")

print(
    f"Accepted {len(all_reports)} reports; all use only "
    "propext, Classical.choice, Quot.sound."
)
