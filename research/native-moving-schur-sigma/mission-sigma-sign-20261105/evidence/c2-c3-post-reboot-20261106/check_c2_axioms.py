#!/usr/bin/env python3
"""Fail-closed axiom audit for the C2 eventual-negativity root."""

import re
import sys
from pathlib import Path

expected_name = (
    "CarrySigmaObstruction."
    "exists_eventually_negative_sigmaPadeD_from_height50_certificate"
)
allowed = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_c2_axioms.py C2_BUILD_LOG")

text = Path(sys.argv[1]).read_text()
reports = re.findall(
    r"^'([^'\n]+)' depends on axioms: \[(.*?)\]$",
    text,
    re.MULTILINE | re.DOTALL,
)
if len(reports) != 1 or reports[0][0] != expected_name:
    raise SystemExit(f"Expected exactly the C2 root, received {[name for name, _ in reports]}")

actual = {
    axiom.strip()
    for axiom in reports[0][1].replace("\n", " ").split(",")
}
if actual != allowed:
    raise SystemExit(f"{expected_name}: expected only standard axioms, received {sorted(actual)}")
if "sorryAx" in text or "declaration uses" in text or "error:" in text:
    raise SystemExit("Lean reported a placeholder or error")

print("Accepted the C2 root: propext, Classical.choice, Quot.sound only.")
