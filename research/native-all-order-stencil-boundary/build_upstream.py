#!/usr/bin/env python3
"""Rebuild the unchanged source/TFVD ancestors actually imported."""
from pathlib import Path
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parent
repo = root.parents[1]
base = "a020c1f0165cf5ff80100d5508ce42d7d5ab8f1d"
records = {}
schedule = [
    ("native-vertical-synthesis", ["SchurBound", "NativeSynthesis", "Quadratures"]),
    ("native-tfvd-completed-transport", ["ShiftTransport", "PhysicalTfvd", "CoefficientPorts",
                                         "CompletionCommutator", "CompletedSourceBridge"]),
    ("native-commutator-mixed-control", ["NativeWeightLaw", "NullCommutator", "MixedReduction", "NativeJets", "GreenSeed"]),
    ("native-critical-tfvd-cancellation", ["ResponseFlux", "CriticalVectors", "ResponseTaylor", "PhysicalKernels", "SectorExpansion", "Cancellation"]),
    ("native-curvature-green-factor", ["ComplementNorm", "CurvatureKernel", "NativeCoefficient", "FourthBoundaryDefect"]),
    ("native-quartic-boundary-sign", ["BoundaryPolynomial", "BoundaryFactor", "QuarticCoefficient"]),
    ("native-linear-tfvd-traces", ["FiniteTraces", "PhysicalNumerator", "GreenPairing"]),
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
