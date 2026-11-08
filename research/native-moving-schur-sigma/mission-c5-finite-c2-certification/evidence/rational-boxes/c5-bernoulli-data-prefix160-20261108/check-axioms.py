#!/usr/bin/env python3
from __future__ import annotations

import re
import sys
from pathlib import Path

if len(sys.argv) != 2:
    raise SystemExit("usage: check-axioms.py AUDIT_LOG")

log = Path(sys.argv[1]).read_text()
reports = re.findall(
    r"'CarrySigmaObstruction\.c5BernoulliPrimeTable_160_eq_data' depends on axioms: \[([^\]]+)\]",
    log,
)
allowed = {"propext", "Classical.choice", "Quot.sound"}
if len(reports) != 1:
    raise SystemExit(f"expected one axiom report, got {len(reports)}")
found = {item.strip() for item in reports[0].split(",")}
if found != allowed:
    raise SystemExit(f"unexpected axiom set: {sorted(found)}")
for forbidden in ("sorryAx", "native_decide"):
    if forbidden in log:
        raise SystemExit(f"forbidden marker found: {forbidden}")
if "error:" in log:
    raise SystemExit("Lean error found in audit log")
print("AXIOM_AUDIT=PASS")
print("AXIOMS=propext,Classical.choice,Quot.sound")
