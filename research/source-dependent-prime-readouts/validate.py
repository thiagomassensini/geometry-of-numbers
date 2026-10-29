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

momentos = Path("/home/thlinux/momentos")
momentos_before = output(["git", "status", "--porcelain=v1"], momentos)
protected_momentos_path = momentos/"AUDITORIA_CORRECTED_MOMENTS_VS_CANONICAL_RECURRENCE.md"
protected_momentos_hash = sha(protected_momentos_path)
operator_before = output(["git", "status", "--porcelain=v1"], operator)
protected = {
    str(operator / "CarrySelfAdjointOperator/C2OddTfvdTransport.lean"):
        sha(operator / "CarrySelfAdjointOperator/C2OddTfvdTransport.lean"),
    str(operator / "CarrySelfAdjointOperator/C2OddTfvdTransportAudit.lean"):
        sha(operator / "CarrySelfAdjointOperator/C2OddTfvdTransportAudit.lean"),
}

source_modules = [
"NativeRealComplementTransport","NativePrimeCarryKernelCalibration",
"CompletedNativeCentralChiralQuotientCurvature","CompletedNativeRadialChiralMultiplier",
"CompletedNativePrimosProjectiveMassCrosswalkAudit","RealQuadratureDomainTransport",
"NativeRealFirstQuadratureNaturality","NativeCauchyLaguerreSources"]
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
      "CarrySelfAdjointOperator.NativeRealComplementTransport",
      "CarrySelfAdjointOperator.CompletedNativeCentralChiralQuotientCurvature",
      "CarrySelfAdjointOperator.CompletedNativeRadialChiralMultiplier"], operator)
for module in ["PrimeProjection","PrimeAnalysis","PrimeCanaries","SignedReadoutSplit",
               "PrimeReturnObstruction","MellinKernelDefect","MellinPrimeReadout","Audit"]:
    check(f"lean-{module}", ["bash", "compile_module.sh", module], root)
check("saved-vm-campaign", ["python3", "audit_vm_campaign.py"], root)

check("root-build", ["lake", "build", "--wfail"], repo)
for layer in ["foundation", "geometry", "analysis"]:
    check(f"audit-{layer}", ["bash", f"scripts/audit-{layer}.sh"], repo)
check("base-preserved", ["git", "diff", "--exit-code", "d17aba9dfd0aa53a7b677cbb3da0e1e6213e0a54", "--", ".", ":(exclude)research/source-dependent-prime-readouts/**"], repo)
check("diff-check", ["git", "diff", "--check"], repo)

for path in root.glob("*.lean"):
    source = path.read_text()
    assert not re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*axiom\s", source, re.M), path
assert output(["git", "status", "--porcelain=v1"], momentos) == momentos_before
assert sha(protected_momentos_path) == protected_momentos_hash
assert output(["git", "status", "--porcelain=v1"], operator) == operator_before
for path, digest in protected.items():
    assert sha(Path(path)) == digest, path
for path, digest in source_manifest.items():
    assert sha(operator / path) == digest, path

result = {
    "created_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "geometry_main": output(["git", "rev-parse", "origin/main"], repo),
    "geometry_base": output(["git", "rev-parse", "origin/agent/all-order-binomial-green"], repo),
    "geometry_branch": output(["git", "branch", "--show-current"], repo),
    "momentos_status_preserved": momentos_before,
    "momentos_modified_audit_sha256": protected_momentos_hash,
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
