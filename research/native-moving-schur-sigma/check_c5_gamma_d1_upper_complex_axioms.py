#!/usr/bin/env python3
"""Fail-closed axiom audit for the upper complex node for d=1/10 C5 Gamma enclosure."""
import re
import sys
from pathlib import Path

allowed = {"propext", "Classical.choice", "Quot.sound"}
required = {
    "c5GammaComplexNodeDOneUpperComplexChunk64RealFloor_0",
    "c5GammaComplexNodeDOneUpperComplexChunk64ImagFloor_0",
    "c5GammaComplexNodeDOneUpperComplexCoreScaledReal_eq_chunkSum",
    "c5GammaComplexNodeDOneUpperComplexCoreScaledImag_eq_chunkSum",
    "c5GammaComplexNodeDOneUpperComplexCoreScaled_chunkBounds",
    "c5GammaComplexNodeDOneUpperComplexRealFloorSum_eq",
    "c5GammaComplexNodeDOneUpperComplexImagFloorSum_eq",
    "c5GammaComplexNodeDOneUpperComplexCoreBox_contains",
    "CarrySigmaObstruction.c5GammaComplexNodeDOneUpperComplexPowerArg_normBound",
    "CarrySigmaObstruction.c5GammaComplexNodeDOneUpperComplexPowerBox_contains",
    "CarrySigmaObstruction.c5GammaComplexNodeDOneUpperComplexBox_contains",
    "CarrySigmaObstruction.c5GammaDOneUpper_log2I_absBound",
    "CarrySigmaObstruction.c5GammaDOneUpper_logQ_absBound",
}
pattern = re.compile(
    r"'(?P<name>[^']+)' depends on axioms:\s*\[(?P<axioms>[^\]]*)\]|"
    r"'(?P<free>[^']+)' does not depend on any axioms"
)
if len(sys.argv) != 2:
    raise SystemExit("usage: check_c5_gamma_d1_upper_complex_axioms.py BUILD_LOG_DIR")
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
