#!/usr/bin/env python3
"""Reproduce the exact Lean checks; retain commands, logs and provenance."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

root = Path(__file__).resolve().parent
repo = root.parents[1]
operator = Path("/home/thlinux/carry-self-adjoint-operator")
evidence = root / "evidence"
evidence.mkdir(exist_ok=True)
environment = os.environ.copy()
environment["PATH"] = str(Path.home() / ".elan/bin") + ":" + environment["PATH"]

def output(args, cwd):
    return subprocess.check_output(args, cwd=cwd, env=environment, text=True).strip()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

operator_before = output(["git", "status", "--porcelain=v1"], operator)
protected = {
    str(operator / "CarrySelfAdjointOperator/C2OddTfvdTransport.lean"):
        sha(operator / "CarrySelfAdjointOperator/C2OddTfvdTransport.lean"),
    str(operator / "CarrySelfAdjointOperator/C2OddTfvdTransportAudit.lean"):
        sha(operator / "CarrySelfAdjointOperator/C2OddTfvdTransportAudit.lean"),
}

source_modules = [
    "NativeSourceAllOrderSchur", "CompletedNativeTfvdWronskianMoments",
    "NativeCauchyLaguerreSources", "NativePhysicalGreenResolvent",
    "CompletedC3FullWronskianCentralChiralEnergy", "CompletedGreenDiagonalClosure",
    "NativeIntervalMultiplier", "NativeCompletedFiniteGreenResidual", "NativeIncidenceCauchyPorts",
    "NativeScalarZetaIdentification", "CompletedNativeChiralJetStorageTransport",
    "CompletedNativeProjectiveChiralCarrier", "CompletedNativeProjectiveChiralForwardDifference",
    "CompletedNativeCentralChiralVariation", "CompletedGreenForwardDifferenceVectorLimit",
    "CompletedNativeChiralReturnSourceTrace",
    "CompletedNativeChiralReturnCompletionSplit", "NativeGammaCoupledCompletionObstruction",
    "CompletedNativeRadialChiralMultiplier", "CompletedNativeChiralReturnStorage",
    "CompletedNativeCentralChiralQuotientCurvature", "CompletedNativeChiralPickFactorization",
]
source_manifest = {
    str(Path("CarrySelfAdjointOperator") / f"{module}.lean"):
        sha(operator / "CarrySelfAdjointOperator" / f"{module}.lean")
    for module in source_modules
}

checks = []
def check(label, args, cwd):
    start = time.monotonic()
    log = evidence / f"{label}.log"
    with log.open("w") as stream:
        result = subprocess.run(["/usr/bin/time", "-v", *args], cwd=cwd,
                                env=environment, text=True, stdout=stream, stderr=subprocess.STDOUT)
    checks.append({"label": label, "command": args, "cwd": str(cwd),
                   "exit_code": result.returncode, "seconds": round(time.monotonic()-start, 3),
                   "log": str(log.relative_to(root))})
    (evidence / "validation.json").write_text(json.dumps({"checks": checks}, indent=2) + "\n")
    print(f"{label}: exit {result.returncode}", flush=True)
    if result.returncode:
        raise SystemExit(f"Failed {label}: see {log}")

check("upstream-provenance", ["python3", "record_provenance.py"], root)
check("generate-audit", ["python3", "generate_audit.py"], root)
check("operator-source-build", ["lake", "build", "--wfail",
      "CarrySelfAdjointOperator.NativeCauchyLaguerreSources",
      "CarrySelfAdjointOperator.NativePhysicalGreenResolvent",
      "CarrySelfAdjointOperator.CompletedC3FullWronskianCentralChiralEnergy",
      "CarrySelfAdjointOperator.NativeSourceAllOrderSchur",
      "CarrySelfAdjointOperator.CompletedNativeTfvdWronskianMoments"], operator)
for module in ["JetFourSource","FiveKernel","QuarticExpansion","QuarticLimits","SchurTransport","PrefixRegression","Audit"]:
    check(f"lean-{module}", ["bash", "compile_module.sh", module], root)
check("polarized-four-diagnostic", ["/home/thlinux/miniforge3/bin/python", "probe_polarized_four.py"], root)

check("root-build", ["lake", "build", "--wfail"], repo)
for layer in ["foundation", "geometry", "analysis"]:
    check(f"audit-{layer}", ["bash", f"scripts/audit-{layer}.sh"], repo)
check("base-preserved", ["git", "diff", "--exit-code", "16caee18d2667dc54ab6fdb37750c136b2366b06", "--", ".", ":(exclude)research/polarized-green-jet-four/**"], repo)
check("diff-check", ["git", "diff", "--check"], repo)

for path in root.glob("*.lean"):
    source = path.read_text()
    assert not re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*axiom\s", source, re.M), path
assert output(["git", "status", "--porcelain=v1"], operator) == operator_before
for path, digest in protected.items():
    assert sha(Path(path)) == digest, path
for path, digest in source_manifest.items():
    assert sha(operator / path) == digest, path

result = {
    "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "geometry_main": output(["git", "rev-parse", "origin/main"], repo),
    "geometry_base": output(["git", "rev-parse", "origin/agent/critical-green-finite-part"], repo),
    "geometry_branch": output(["git", "branch", "--show-current"], repo),
    "operator_head": output(["git", "rev-parse", "HEAD"], operator),
    "operator_origin_main": output(["git", "rev-parse", "origin/main"], operator),
    "operator_status_preserved": operator_before,
    "operator_modules_sha256": source_manifest,
    "protected_files_sha256": protected,
    "checks": checks,
    "new_sources_sha256": {path.name: sha(path) for path in sorted(root.glob("*.lean"))},
    "trust_escape_scan": "PASS",
    "operator_sources_and_preexisting_files": "PRESERVED",
}
(evidence / "validation.json").write_text(json.dumps(result, indent=2) + "\n")
print(f"PASS: {len(checks)} commands; no trusted escapes; source preservation verified", flush=True)
