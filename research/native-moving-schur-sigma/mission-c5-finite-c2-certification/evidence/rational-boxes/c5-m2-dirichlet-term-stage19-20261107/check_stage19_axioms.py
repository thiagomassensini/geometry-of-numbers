#!/usr/bin/env python3
"""Fail-closed axiom audit for the five stage-19 theorem roots."""
from pathlib import Path
import re
import sys

log = Path(__file__).with_name("state-stage19-build.log").read_text()
expected = {
    "c5M2Stage19PowerCoarsenExport",
    "c5M2Stage19PowerCorrect",
    "c5M2Stage19TermCoarsenExport",
    "c5M2Stage19SumCorrect",
    "c5RoundedExpStateC_stage19_correct",
}
found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log):
    found[name] = {a.strip() for a in axioms.split(",") if a.strip()}
allowed = {"propext", "Classical.choice", "Quot.sound"}
if "BUILD_EXIT=0" not in log or expected != set(found):
    print(f"FAIL: successful build and exact root set required; found={sorted(found)}")
    sys.exit(1)
for name, axioms in found.items():
    if "sorryAx" in axioms or not axioms <= allowed:
        print(f"FAIL: unexpected axioms for {name}: {sorted(axioms)}")
        sys.exit(1)
print("PASS: all five roots use only propext, Classical.choice, and Quot.sound; no sorryAx")
