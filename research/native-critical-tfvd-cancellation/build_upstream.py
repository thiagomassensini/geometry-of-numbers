#!/usr/bin/env python3
"""Rebuild the unchanged source/TFVD ancestors actually imported."""
from pathlib import Path
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parent
repo = root.parents[1]
base = "35a1035eee70ebb2961b689a71b6d72ff46a41b3"
records = {}
schedule = [
    ("native-vertical-synthesis", ["SchurBound", "NativeSynthesis", "Quadratures"]),
    ("native-tfvd-completed-transport", ["ShiftTransport", "PhysicalTfvd", "CoefficientPorts",
                                         "CompletionCommutator", "CompletedSourceBridge"]),
    ("native-commutator-mixed-control", ["NativeWeightLaw", "NullCommutator", "MixedReduction", "NativeJets", "GreenSeed"]),
]
for directory, modules in schedule:
    for module in modules:
        p = root.parent / directory / f"{module}.lean"
        rel = str(p.relative_to(repo))
        original = subprocess.check_output(["git", "show", base + ":" + rel], cwd=repo)
        assert p.read_bytes() == original, rel
        subprocess.run(["bash", "compile_module.sh", module, str(p)], cwd=root, check=True)
        records[module] = {"source": rel, "source_sha256": hashlib.sha256(original).hexdigest(),
            "olean_sha256": hashlib.sha256((p.parent / ".cache" / f"{module}.olean").read_bytes()).hexdigest()}
(root / "evidence").mkdir(exist_ok=True)
(root / "evidence/upstream.json").write_text(json.dumps({"base": base, "modules": records}, indent=2) + "\n")
print("PASS: unchanged source/TFVD ancestors rebuilt from their exact base.")
