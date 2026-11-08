#!/usr/bin/env python3
"""Fail-closed source and transitive-axiom audit for the B2 scale/root exports."""

from __future__ import annotations

import re
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
SOURCE_ROOT = HERE.parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REPORT_PATTERN = re.compile(
    r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]"
    r"|'([^']+)' does not depend on any axioms"
)
EXPECTED_BY_LOG = {
    "B2.2-SigmaCentralTenHeightScaleBridge.log": {
        "CarrySigmaObstruction.sigmaHeight50_ten_height_scales",
        "CarrySigmaObstruction.exists_sigmaHeight50_scale_hbox",
    },
    "B2.3-SigmaCentralTenHeightRootBridge.log": {
        "CarrySigmaObstruction.sigmaHeight50_original_characteristic_roots",
    },
}
SOURCE_FILES = {
    "SigmaHeight50Integration.lean",
    "SigmaCentralTenHeightScaleBridge.lean",
    "SigmaCentralTenHeightRootBridge.lean",
}
PUBLIC_AXIOM_PRINTS = {
    "CarrySigmaObstruction.sigmaHeight50_ten_height_scales",
    "CarrySigmaObstruction.exists_sigmaHeight50_scale_hbox",
    "CarrySigmaObstruction.sigmaHeight50_original_characteristic_roots",
}


def fail(message: str) -> None:
    raise SystemExit(f"B2 axiom audit failed: {message}")


if len(sys.argv) != 1:
    fail("run without arguments from any directory")

all_sources: dict[str, str] = {}
for filename in sorted(SOURCE_FILES):
    path = SOURCE_ROOT / filename
    if not path.is_file():
        fail(f"missing source file: {path}")
    source = path.read_text()
    all_sources[filename] = source
    if re.search(r"\b(?:sorry|sorryAx|admit|native_decide)\b", source):
        fail(f"placeholder or native_decide found in {filename}")
    if re.search(r"\baxiom\b", source):
        fail(f"axiom token found in {filename}")

for theorem in sorted(PUBLIC_AXIOM_PRINTS):
    local_name = theorem.rsplit(".", 1)[-1]
    if not any(
        f"#print axioms {local_name}" in source
        for source in all_sources.values()
    ):
        fail(f"missing source audit directive for {theorem}")

accepted_reports = 0
for log_name, expected in EXPECTED_BY_LOG.items():
    path = HERE / log_name
    if not path.is_file():
        fail(f"missing successful build log: {path}")
    text = path.read_text()
    if re.search(r"\bsorryAx\b|declaration uses [`']sorry[`']|\berror(?:\([^\n)]*\))?:", text):
        fail(f"placeholder or Lean error found in {log_name}")
    reports: dict[str, set[str]] = {}
    for dependent, axioms, axiom_free in REPORT_PATTERN.findall(text):
        name = dependent or axiom_free
        actual = {item.strip() for item in axioms.split(",") if item.strip()}
        if name in reports:
            fail(f"duplicate axiom report for {name} in {log_name}")
        reports[name] = actual
    marker_count = text.count("depends on axioms:") + text.count(
        "does not depend on any axioms"
    )
    if marker_count != len(reports):
        fail(f"malformed or truncated axiom report in {log_name}")
    if set(reports) != expected:
        fail(
            f"{log_name}: expected exactly {sorted(expected)}, "
            f"received {sorted(reports)}"
        )
    for name, actual in reports.items():
        unexpected = actual - ALLOWED_AXIOMS
        if unexpected:
            fail(f"{name}: unexpected axioms {sorted(unexpected)}")
    accepted_reports += len(reports)

print(
    f"Accepted {accepted_reports} scale/root reports; source scan found no "
    "sorry, admit, native_decide, or axiom declarations."
)
