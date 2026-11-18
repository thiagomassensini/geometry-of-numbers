#!/usr/bin/env python3
"""Read-only completion check for the ninth-order GoN/CSA Lean audit logs.

Must be run after compiling the listed Lean declarations. It checks
frozen source script syntax separately; it does NOT recompile the Lean proof.
"""
import pathlib
import re
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parents[2]
audit = root / "research/projective-chiral-complex-cauchy/validate-physical-nine.sh"
paths = [
    pathlib.Path("/tmp/gon-c2-nine-physical-validation.log"),
    pathlib.Path("/tmp/gon-c2-nine-module-validation.log"),
    pathlib.Path("/tmp/gon-c2-nine-additional-sign-audit.log"),
]
for f in [audit, *paths]:
    if not f.is_file():
        sys.exit(f"FAIL: required audit evidence absent: {f}")
subprocess.run(["bash", "-n", str(audit)], check=True)
script = audit.read_text()
m = re.search(r"for decl in \\\n(.*?); do\n", script, re.S)
if not m:
    sys.exit("FAIL: declaration manifest not found in shell audit")
decls = []
for line in m.group(1).splitlines():
    name = line.strip().removesuffix("\\").strip()
    if name:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name):
            sys.exit(f"FAIL: malformed manifest entry: {line!r}")
        decls.append(name)
if not 50 <= len(decls) <= 100:
    sys.exit(f"FAIL: unexpected manifest length: {len(decls)}")

text = "\n".join(f.read_text() for f in paths)
if re.search(r"error:|sorryAx|\badmit\b", text):
    sys.exit("FAIL: Lean logs contain error, sorryAx, or admit")
for name in decls:
    rx = rf"'(?:[A-Za-z_][A-Za-z_0-9]*\.)*{re.escape(name)}' depends on axioms: \[([^\]]*)\]"
    hits = re.findall(rx, text)
    if not hits:
        sys.exit(f"FAIL: no Lean axiom-print evidence for {name}")
    for block in hits:
        axs = {s.strip() for s in block.split(",")}
        if axs - {"propext", "Classical.choice", "Quot.sound"}:
            sys.exit(f"FAIL: non-standard axioms for {name}: {sorted(axs)}")

for p in [
    "PhysicalPickNineEvenSourceHankel",
    "PhysicalPickNineEvenSignBridge",
    "PhysicalPickNineSchurDetLaw",
    "PhysicalPickNineRelativeSourceAngle",
    "PhysicalPickNinePhysicalBoundary",
    "PhysicalPickNineNative",
    "PhysicalPickNineCongruence",
    "PhysicalPickNineSign",
    "PhysicalPickNineFinal",
]:
    olean = root / ".lake/build/lib/lean" / (p + ".olean")
    if not olean.is_file() or olean.stat().st_size <= 0:
        sys.exit(f"FAIL: missing compiled object: {olean}")
for name in [
    "physicalC2RadialPickMatrix_nine_eventually_posDef",
    "physicalC2RadialDefectMatrix_nine_eventually_posDef",
    "nativeSourceNineCompleteBoundaryEnergy_pos",
    "nativeSourceNineReturn_eventually_contractive",
]:
    core = paths[0].read_text()
    if f"{name}' depends on axioms" not in core:
        sys.exit(f"FAIL: key physical theorem missing from full Lean recompile log: {name}")
print(f"PASS: {len(decls)} ninth-order and historical audit declarations verified")
print("PASS: no Lean errors or non-standard axioms in sequential compilation logs")
print("PASS: physical Pick9, HB defect9, source boundary9/return9 from full chain")
print("PASS: exact Schur determinant law and normalized source fractions from supplementary compiler run")
print("PASS: current audit source shell syntax; original 9 modules have compiled .olean files")
print("NOTE: this verification reads existing full compilation logs; it does not claim a clean exit from the original hot-edited wrapper.")
