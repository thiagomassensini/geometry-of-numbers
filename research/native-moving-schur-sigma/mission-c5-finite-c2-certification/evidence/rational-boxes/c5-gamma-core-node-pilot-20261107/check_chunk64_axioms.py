#!/usr/bin/env python3
"""Fail-closed audit for the 16 rational Gamma chunk floors and box proof."""
import re
import sys
from pathlib import Path

EXPECTED = [f"c5GammaChunk64_{i}_floor" for i in range(16)] + [
    "c5GammaCoreNodePilotScaled_eq_chunkSum",
    "c5GammaCoreNodePilotScaled_chunkBounds",
    "c5GammaCoreChunkFloorSum_eq",
    "c5GammaCoreNodePilotChunkBox_contains",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

if len(sys.argv) != 2:
    raise SystemExit("usage: check_chunk64_axioms.py AXIOM_AUDIT_LOG")
log_path = Path(sys.argv[1])
log = log_path.read_text()
if re.search(r"\b(error:|sorryAx|native_decide|BUILD_EXIT=[1-9])", log):
    raise SystemExit("audit log contains an error or a forbidden axiom")
rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
seen = [name for name, _ in rows]
if seen != EXPECTED:
    raise SystemExit(f"unexpected/missing roots: got {seen!r}")
for name, axioms_text in rows:
    axioms = {item.strip() for item in axioms_text.split(",") if item.strip()}
    if not axioms <= ALLOWED:
        raise SystemExit(f"{name} has disallowed axioms: {sorted(axioms - ALLOWED)}")
print(f"PASS: {len(rows)} roots; axioms limited to {', '.join(sorted(ALLOWED))}")
