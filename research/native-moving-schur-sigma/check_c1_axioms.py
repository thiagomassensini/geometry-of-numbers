#!/usr/bin/env python3
"""Fail-closed axiom audit for the C1 proof and its source certificate."""

import re
import sys
from pathlib import Path

required = {
    "CarrySigmaObstruction.exists_sigmaMatrix_negative_direction_of_zero",
    "CarrySigmaObstruction.completedNativeCharacteristicContinuation_eq_native",
    "CarrySigmaObstruction.completedNativeCharacteristicContinuation_zero_iff_zeta",
    "CarrySigmaObstruction.certified_sigma_negative_direction_of_nonzero_small_shift",
    "HardyFirstZero.first_zero_on_line",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_c1_axioms.py BUILD_LOG")
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
