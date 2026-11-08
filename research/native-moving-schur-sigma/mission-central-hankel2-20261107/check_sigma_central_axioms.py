#!/usr/bin/env python3
"""Fail closed unless the B1 Lean axiom report contains only standard axioms."""

from __future__ import annotations

import re
import sys
from pathlib import Path


EXPECTED_THEOREMS = {
    "CarrySigmaCentral.finiteMoment_hankel2_eq_pairMoment",
    "CarrySigmaCentral.hankel2_add_error_expansion",
    "CarrySigmaCentral.hankel2_error_abs_bound",
    "CarrySigmaCentral.mainLower_le_tenMode_hankel2",
    "CarrySigmaCentral.early_margin_pos",
    "CarrySigmaCentral.ratio_lt_one_of_four_le",
    "CarrySigmaCentral.central_hankel2_pos_of_ten_boxes_and_tail",
    "CarrySigmaPade.sigmaPadeD_center_pos_of_conditional_ten_mode_tail",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

REPORT = re.compile(
    r"(?P<name>CarrySigma(?:Central|Pade)\.[A-Za-z0-9_']+)"
    r".*?depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
)
NO_AXIOMS = re.compile(
    r"(?P<name>CarrySigma(?:Central|Pade)\.[A-Za-z0-9_']+)"
    r".*?does not depend on any axioms"
)


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {Path(sys.argv[0]).name} AXIOM_AUDIT_LOG", file=sys.stderr)
        return 2

    log_path = Path(sys.argv[1])
    # Lean quotes theorem names and may wrap one axiom list across lines.
    # Flatten whitespace and strip the surrounding quotes before comparison.
    text = " ".join(log_path.read_text(encoding="utf-8").split())
    found: dict[str, set[str]] = {}
    for match in REPORT.finditer(text):
        axioms = {item.strip() for item in match.group("axioms").split(",") if item.strip()}
        found[match.group("name").strip("'")] = axioms
    for match in NO_AXIOMS.finditer(text):
        found[match.group("name").strip("'")] = set()

    missing = EXPECTED_THEOREMS - found.keys()
    if missing:
        print(f"FAIL: missing axiom reports for: {', '.join(sorted(missing))}", file=sys.stderr)
        return 1

    failures = {
        theorem: axioms - ALLOWED_AXIOMS
        for theorem, axioms in found.items()
        if theorem in EXPECTED_THEOREMS and axioms - ALLOWED_AXIOMS
    }
    if failures or "sorryAx" in text or re.search(r"\b(admit|sorry)\b", text):
        for theorem, axioms in sorted(failures.items()):
            print(f"FAIL: {theorem} has unexpected axioms: {', '.join(sorted(axioms))}", file=sys.stderr)
        if "sorryAx" in text or re.search(r"\b(admit|sorry)\b", text):
            print("FAIL: audit log mentions sorry/admit", file=sys.stderr)
        return 1

    print(f"PASS: {len(EXPECTED_THEOREMS)} B1 theorem closures use only allowed standard axioms")
    for theorem in sorted(EXPECTED_THEOREMS):
        print(f"{theorem}: {', '.join(sorted(found[theorem])) or '(none)'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
