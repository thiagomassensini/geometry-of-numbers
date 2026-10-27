#!/usr/bin/env python3
"""Rebuild the unchanged source/TFVD ancestors actually imported."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

root = Path(__file__).resolve().parent
repo = root.parents[1]
base = "114c220b4e187f80e6645f354fd0de7e08444768"
records = {}
verify_only = "--verify-existing" in sys.argv
resume_bootstrap = "--resume-bootstrap" in sys.argv
prior = json.loads((root / "evidence/upstream.json").read_text())["modules"] if verify_only else {}
schedule = [
    ("native-vertical-synthesis", ["SchurBound", "NativeSynthesis", "Quadratures"]),
    ("native-tfvd-completed-transport", ["ShiftTransport", "PhysicalTfvd", "CoefficientPorts",
                                         "CompletionCommutator", "CompletedSourceBridge"]),
    ("native-commutator-mixed-control", ["NativeWeightLaw", "NullCommutator", "MixedReduction", "NativeJets", "GreenSeed"]),
    ("native-critical-tfvd-cancellation", ["ResponseFlux", "CriticalVectors", "ResponseTaylor", "PhysicalKernels", "SectorExpansion", "Cancellation"]),
    ("native-curvature-green-factor", ["ComplementNorm", "CurvatureKernel", "NativeCoefficient", "FourthBoundaryDefect"]),
    ("native-linear-tfvd-traces", ["FiniteTraces", "PhysicalNumerator", "GreenPairing"]),
    ("native-all-order-stencil-boundary", ["Stencil"]),
    ("native-cubic-tfvd-numerator", ["CubicNumerator", "CubicGreen", "CriticalFamily"]),
]
for directory, modules in schedule:
    for module in modules:
        p = root.parent / directory / f"{module}.lean"
        rel = str(p.relative_to(repo))
        original = subprocess.check_output(["git", "show", base + ":" + rel], cwd=repo)
        assert p.read_bytes() == original, rel
        if verify_only:
            assert prior[module]["source_sha256"] == hashlib.sha256(original).hexdigest(), rel
            assert prior[module]["olean_sha256"] == hashlib.sha256((p.parent / ".cache" / f"{module}.olean").read_bytes()).hexdigest(), rel
        elif not (resume_bootstrap and (p.parent / ".cache" / f"{module}.olean").is_file()):
            subprocess.run(["bash", "compile_module.sh", module, str(p)], cwd=root, check=True)
        records[module] = {"source": rel, "source_sha256": hashlib.sha256(original).hexdigest(),
            "olean_sha256": hashlib.sha256((p.parent / ".cache" / f"{module}.olean").read_bytes()).hexdigest()}
(root / "evidence").mkdir(exist_ok=True)
(root / "evidence/upstream.json").write_text(json.dumps({"base": base, "modules": records}, indent=2) + "\n")
print("PASS: unchanged source/TFVD ancestors " + ("checked against source/olean hashes from the recorded build." if verify_only else "rebuilt from their exact base."))
