#!/usr/bin/env python3
"""Focused kernel builds, explicit axiom audit, and repository regressions."""
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys
import time

task = pathlib.Path(__file__).resolve().parent
repo = task.parent.parent
evidence = task / "evidence"
evidence.mkdir(exist_ok=True)
env = os.environ.copy()
env["PATH"] = "/home/thlinux/.elan/bin:" + env["PATH"]

def read(*args, cwd=repo):
    return subprocess.check_output(args, cwd=cwd, env=env, text=True).strip()

base = "59e53d863f4ef0ad998b0eb19fd3891c9839cc35"
operator = repo.parent / "carry-self-adjoint-operator"
protected = [operator / "CarrySelfAdjointOperator" / name for name in
             ["C2OddTfvdTransport.lean", "C2OddTfvdTransportAudit.lean"]]
preflight = {
    "base": base,
    "branch": read("git", "branch", "--show-current"),
    "head_before_commit": read("git", "rev-parse", "HEAD"),
    "origin_main": read("git", "rev-parse", "origin/main"),
    "operator_head": read("git", "rev-parse", "HEAD", cwd=operator),
    "operator_status": read("git", "status", "--short", cwd=operator),
    "protected_untracked_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in protected},
    "toolchain": (repo / "lean-toolchain").read_text().strip(),
    "manifest_sha256": hashlib.sha256((repo / "lake-manifest.json").read_bytes()).hexdigest(),
}
(evidence / "preflight.json").write_text(json.dumps(preflight, indent=2) + "\n")
modules = ["MomentFunctional", "PolynomialCoordinates", "JacobiLogic", "Controls", "NativeApplication", "SchurLogic", "Audit"]
for module in modules:
    source = (task / f"{module}.lean").read_text()
    if re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", source, re.M):
        raise SystemExit(f"Untrusted source token in {module}")

relative = str(task.relative_to(repo))
commands = [
    ("focused-build", ["lake", "build", "--wfail",
        "GeometryOfNumbers.Analysis.LogarithmicMomentHankel",
        "GeometryOfNumbers.Analysis.FiniteJacobiTransport",
        "GeometryOfNumbers.Analysis.CanonicalLDLWhitening",
        "GeometryOfNumbers.Analysis.CanonicalFiniteHeight",
        "GeometryOfNumbers.Analysis.CarryMaterialSourceFactor"]),
]
commands += [(f"kernel-{module}", ["bash", f"{relative}/compile_module.sh", module]) for module in modules]
commands += [
    ("root-build", ["lake", "build", "--wfail"]),
    ("foundation-audit", ["bash", "scripts/audit-foundation.sh"]),
    ("geometry-audit", ["bash", "scripts/audit-geometry.sh"]),
    ("analysis-audit", ["bash", "scripts/audit-analysis.sh"]),
    ("twelve-source-regression", ["bash", "research/sixth-odd-twelve-sources/compile_module.sh", "Regression"]),
    ("historical-files-unchanged", ["git", "diff", "--exit-code", base, "--", ".", ":(exclude)research/native-moment-orthogonalization-audit"]),
]
research_only = "--research-only" in sys.argv
if research_only:
    commands = [(name, cmd) for name, cmd in commands if name.startswith("kernel-") or name == "historical-files-unchanged"]
checks_name = "checks-research.json" if research_only else "checks.json"
results = []
for name, command in commands:
    started = time.monotonic()
    with (evidence / f"{name}.log").open("w") as log:
        result = subprocess.run(command, cwd=repo, env=env, stdout=log, stderr=subprocess.STDOUT)
    results.append({"name": name, "command": command, "exit_code": result.returncode,
                    "seconds": round(time.monotonic() - started, 3)})
    (evidence / checks_name).write_text(json.dumps(results, indent=2) + "\n")
    print(f"{name}: {'PASS' if result.returncode == 0 else 'FAIL'}", flush=True)
    if result.returncode:
        print((evidence / f"{name}.log").read_text()[-8000:], flush=True)
        raise SystemExit(result.returncode)
for path in protected:
    assert hashlib.sha256(path.read_bytes()).hexdigest() == preflight["protected_untracked_sha256"][str(path)]
assert read("git", "rev-parse", "origin/main") == preflight["origin_main"]
assert read("git", "rev-parse", "HEAD", cwd=operator) == preflight["operator_head"]
print(f"PASS: {len(results)} checks; main, pins and operator user files preserved", flush=True)
