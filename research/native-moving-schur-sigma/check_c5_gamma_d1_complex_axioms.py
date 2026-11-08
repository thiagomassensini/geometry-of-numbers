#!/usr/bin/env python3
"""Fail-closed axiom audit for the d=1/10 complex C5 Gamma enclosure."""
import re
import sys
from pathlib import Path

allowed = {"propext", "Classical.choice", "Quot.sound"}
required = {
    "c5GammaComplexNodeDOneComplexChunk64RealFloor_0",
    "c5GammaComplexNodeDOneComplexChunk64ImagFloor_0",
    "c5GammaComplexNodeDOneComplexCoreScaledReal_eq_chunkSum",
    "c5GammaComplexNodeDOneComplexCoreScaledImag_eq_chunkSum",
    "c5GammaComplexNodeDOneComplexCoreScaled_chunkBounds",
    "c5GammaComplexNodeDOneComplexRealFloorSum_eq",
    "c5GammaComplexNodeDOneComplexImagFloorSum_eq",
    "c5GammaComplexNodeDOneComplexCoreBox_contains",
    "CarrySigmaObstruction.c5GammaComplexNodeDOneComplexPowerArg_normBound",
    "CarrySigmaObstruction.c5GammaComplexNodeDOneComplexPowerBox_contains",
    "CarrySigmaObstruction.c5GammaComplexNodeDOneComplexBox_contains",
}
pattern = re.compile(
    r"'(?P<name>[^']+)' depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"'(?P<free>[^']+)' does not depend on any axioms"
)
if len(sys.argv) != 2:
    raise SystemExit("usage: check_c5_gamma_d1_complex_axioms.py BUILD_LOG_DIR")
log_dir = Path(sys.argv[1])
logs = sorted(log_dir.glob("*.log"))
if not logs:
    raise SystemExit(f"no build logs in {log_dir}")
reports = []
for path in logs:
    text = path.read_text()
    if "BUILD_EXIT=0" not in text or re.search(r"BUILD_EXIT=(?!0\b)", text):
        raise SystemExit(f"{path}: build did not finish successfully")
    if re.search(r"\bsorryAx\b|declaration uses [`']sorry[`']|error(?:\([^\n)]*\))?:", text):
        raise SystemExit(f"{path}: Lean reported a placeholder or error")
    matches = []
    for match in pattern.finditer(text):
        if match.group("name"):
            name = match.group("name")
            axioms = {x.strip() for x in match.group("axioms").split(",") if x.strip()}
        else:
            name, axioms = match.group("free"), set()
        unexpected = axioms - allowed
        if unexpected:
            raise SystemExit(f"{name}: unexpected axioms {sorted(unexpected)}")
        matches.append((name, axioms))
    report_count = text.count("depends on axioms:") + text.count("does not depend on any axioms")
    if report_count != len(matches):
        raise SystemExit(f"{path}: malformed or truncated axiom report")
    reports.extend(matches)
names = {name for name, _ in reports}
missing = required - names
if missing:
    raise SystemExit(f"missing audited declarations: {sorted(missing)}")
print(f"Accepted {len(reports)} reports; only propext, Classical.choice, Quot.sound.")
