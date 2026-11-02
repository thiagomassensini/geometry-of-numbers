#!/usr/bin/env python3
"""Check every new theorem's #print axioms against the allowed base."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
log = Path(sys.argv[1]) if len(sys.argv) > 1 else root / "evidence/new-audit.log"
names = set()
for source in root.glob("*.lean"):
    if source.name == "Audit.lean":
        continue
    names.update("CarryCriticalRadialMargin." + n for n in
                 re.findall(r"^theorem\s+([A-Za-z0-9_]+)", source.read_text(), re.M))
entries = re.findall(r"'(CarryCriticalRadialMargin\.[^']+)' depends on axioms:\s*\[([^\]]*)\]",
                     log.read_text(), re.S)
allowed = {"propext", "Classical.choice", "Quot.sound"}
assert len(entries) == len(names) and {n for n, _ in entries} == names
for name, axioms in entries:
    actual = {x.strip() for x in axioms.split(",") if x.strip()}
    assert actual <= allowed, (name, sorted(actual - allowed))
assert "Transitive source audit: 4 roots;" in log.read_text()
print(f"PASS: {len(names)} theorem axiom footprints, four transitive source roots")
