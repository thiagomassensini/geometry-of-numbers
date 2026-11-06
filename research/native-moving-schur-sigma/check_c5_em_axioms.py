#!/usr/bin/env python3
"""Fail-closed axiom audit for the high-order Euler–Maclaurin checkpoint."""

import re
import sys
from pathlib import Path

required = {
    "SigmaC5Zeta.natPowSeries_le_two",
    "SigmaC5Zeta.bernoulliFun_abs_le_four_factorial_div_six_pow",
    "SigmaC5Zeta.emBernoulliCell",
    "SigmaC5Zeta.zeta_em_high_of_two_lt",
    "SigmaC5Zeta.zeta_em_high",
    "SigmaC5Zeta.zeta_em_high_real",
    "SigmaC5Zeta.emZetaHighTail_norm_le",
    "SigmaC5Zeta.emZetaHighTail_norm_le_node",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}
pattern = re.compile(
    r"'(?P<name>[^']+)' depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"'(?P<free>[^']+)' does not depend on any axioms"
)

if len(sys.argv) < 2:
    raise SystemExit("usage: check_c5_em_axioms.py BUILD_AND_AXIOM_LOG [LOG ...]")

reports = []
for filename in sys.argv[1:]:
    text = Path(filename).read_text()
    if "BUILD_EXIT=0" not in text or re.search(r"\bBUILD_EXIT=(?!0\b)", text):
        raise SystemExit(f"{filename}: missing successful build marker")
    matches = list(pattern.finditer(text))
    report_count = text.count("depends on axioms:") + text.count(
        "does not depend on any axioms"
    )
    if report_count != len(matches):
        raise SystemExit(f"{filename}: malformed or truncated axiom report")
    if re.search(r"\bsorryAx\b|declaration uses [`']sorry[`']|\berror(?:\([^\n)]*\))?:", text):
        raise SystemExit(f"{filename}: Lean reported a placeholder or error")
    for match in matches:
        name = match.group("name") or match.group("free")
        axioms = {
            item.strip()
            for item in (match.group("axioms") or "").split(",")
            if item.strip()
        }
        unexpected = axioms - allowed
        if unexpected:
            raise SystemExit(f"{name}: unexpected axioms {sorted(unexpected)}")
        reports.append(name)

if len(reports) != len(required) or set(reports) != required:
    raise SystemExit(
        f"required exactly {len(required)} reports; got {len(reports)}: "
        f"missing={sorted(required - set(reports))}, "
        f"extra={sorted(set(reports) - required)}"
    )

print(
    f"Accepted exactly {len(reports)} reports; all use only "
    "propext, Classical.choice, Quot.sound."
)
