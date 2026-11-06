#!/usr/bin/env python3
"""Fail-closed axiom audit for the C5 exact-rational interval proofs."""

import re
import sys
from pathlib import Path

required = {
    "CarrySigmaObstruction.sigmaRatBallContains_mul",
    "CarrySigmaObstruction.sigmaRatBallContains_pow",
    "CarrySigmaObstruction.sigmaFiniteScaledMomentBall_valid_bounded",
    "CarrySigmaObstruction.sigmaFiniteScaledMomentBall_contains_of_recurrence",
    "CarrySigmaObstruction.sigmaFiniteScaledMomentBallMinor_contains",
    "CarrySigmaObstruction.sigmaC00495Minor_lower_pos",
    "CarrySigmaObstruction.sigmaC00495Minor_final_neg",
    "CarrySigmaObstruction.sigmaC01Minor_lower_pos",
    "CarrySigmaObstruction.sigmaC01Minor_final_neg",
    "CarrySigmaObstruction.sigmaC00495_scaled_moment_boxes",
    "CarrySigmaObstruction.sigmaC01_scaled_moment_boxes",
    "CarrySigmaObstruction.sigmaPadeD_signs_at_99_2000_of_source_boxes",
    "CarrySigmaObstruction.sigmaPadeD_signs_at_1_10_of_source_boxes",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_c5_rational_axioms.py AXIOM_AUDIT_LOG")
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
