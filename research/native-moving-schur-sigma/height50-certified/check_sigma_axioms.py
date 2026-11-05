#!/usr/bin/env python3
"""Fail-closed axiom audit for the compiled bridge and closed integration."""

import re
import sys
from pathlib import Path

expected = {
    "RHHeight.rh_height_fifty",
    "RHHeight.zero_count_fifty",
    "RHHeight.rh_up_to_height_fiftytwo",
    "HardyFirstZero.first_zero_on_line",
    "HardyTenZeros.ten_zeros_on_line_below_fifty",
    *{f"HardyTenZeros.zero_in_{tag}" for tag in (
        "2102", "2501", "3042", "3293", "3758", "4091", "4332", "4800", "4977"
    )},
    "CarrySigmaObstruction.exists_firstSigmaDisplacedProductIsolation_from_height50_certificate",
    "CarrySigmaObstruction.exists_firstSigmaHeight50PadeRecovery_from_certificate",
    "CarrySigmaObstruction.exists_eventually_negative_sigmaPadeD_from_height50_certificate",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_sigma_axioms.py INTEGRATION_LOG")
text = Path(sys.argv[1]).read_text()
reports = re.findall(r"^'([^'\n]+)' depends on axioms: \[([^\]]*)\]$", text, re.MULTILINE)
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
print(f"Accepted all {len(expected)} reports: propext, Classical.choice, Quot.sound only.")
