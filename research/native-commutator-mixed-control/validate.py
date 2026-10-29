#!/usr/bin/env python3
"""Focused warning-as-error builds, kernel audits and source-preservation checks."""
from pathlib import Path
import hashlib
import gzip
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
checks = []

def output(args, cwd):
    return subprocess.check_output(args, cwd=cwd, env=environment, text=True).strip()

def check(label, args, cwd):
    start = time.monotonic()
    log = evidence / f"{label}.log"
    with log.open("w") as stream:
        result = subprocess.run(["/usr/bin/time", "-v", *args], cwd=cwd, env=environment,
                                text=True, stdout=stream, stderr=subprocess.STDOUT)
    raw = log.read_bytes()
    normalized = b"\n".join(line.rstrip(b" \t\r") for line in raw.split(b"\n"))
    raw_record = {}
    if normalized != raw:
        raw_path = log.with_suffix(".raw.log.gz")
        raw_path.write_bytes(gzip.compress(raw, mtime=0))
        log.write_bytes(normalized)
        raw_record = {"raw_log": str(raw_path.relative_to(root)),
                      "raw_log_sha256": hashlib.sha256(raw).hexdigest(),
                      "text_normalization": "trailing whitespace only"}
    checks.append({"label": label, "command": args, "cwd": str(cwd),
                   "exit_code": result.returncode, "seconds": round(time.monotonic() - start, 3),
                   "log": str(log.relative_to(root)), **raw_record})
    (evidence / "validation.json").write_text(json.dumps({"checks": checks}, indent=2) + "\n")
    print(f"{label}: exit {result.returncode}", flush=True)
    if result.returncode:
        raise SystemExit(f"Failed {label}: {log}")

check("source-provenance", ["python3", "record_provenance.py"], root)
baseline = json.loads((evidence / "source-provenance.json").read_text())
check("upstream-synthesis-build", ["python3", "build_upstream.py"], root)
check("generate-audit", ["python3", "generate_audit.py"], root)
check("operator-source-build", ["lake", "build", "--wfail",
      "CarrySelfAdjointOperator.NativePhysicalGreenResolvent",
      "CarrySelfAdjointOperator.CompletedNativeChiralJetStorageTransport",
      "CarrySelfAdjointOperator.CompletedNativeCentralProductDressingAudit"], operator)
for module in ["NativeWeightLaw", "NullCommutator", "MixedReduction", "NativeJets", "GreenSeed", "SeedMixedLimit", "Audit"]:
    check(f"lean-{module}", ["bash", "compile_module.sh", module], root)
check("root-build", ["lake", "build", "--wfail"], repo)
for layer in ["foundation", "geometry", "analysis"]:
    check(f"audit-{layer}", ["bash", f"scripts/audit-{layer}.sh"], repo)
check("base-preserved", ["git", "diff", "--exit-code", baseline["base"], "--", ".",
      ":(exclude)research/native-commutator-mixed-control/**"], repo)
check("diff-check", ["git", "diff", "--check"], repo)
for p in root.glob("*.lean"):
    assert not re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*axiom\s", p.read_text(), re.M), p
for path, digest in baseline["protected_sha256"].items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest, path
for path, digest in baseline["geometry_tfvd_sources_sha256"].items():
    assert hashlib.sha256((repo / path).read_bytes()).hexdigest() == digest, path
for path, digest in baseline["source_sha256"].items():
    assert hashlib.sha256((operator / path).read_bytes()).hexdigest() == digest, path
for path, expected in [(operator, baseline["operator_status"]),
                       (Path("/home/thlinux/momentos"), baseline["momentos_status"])]:
    assert output(["git", "status", "--porcelain=v1"], path) == expected
assert output(["git", "rev-parse", "main"], repo) == baseline["main"]
assert output(["git", "rev-parse", "origin/main"], repo) == baseline["origin_main"]
for package, revision in baseline["pins"].items():
    assert output(["git", "rev-parse", "HEAD"], operator / ".lake/packages" / package) == revision
assert hashlib.sha256((operator / ".lake/packages/CPFormal/CPFormal/Analytic/CpNativeGpreTowerNorm.lean").read_bytes()).hexdigest() == baseline["native_tower_source_sha256"]
(evidence / "preservation.json").write_text(json.dumps({"PASS": True,
    "source_unchanged": True, "pins_unchanged": True, "main_unchanged": True,
    "old_dirty_work_preserved": True, "no_new_trust_escapes": True}, indent=2) + "\n")
print(f"PASS: {len(checks)} checks, native sources and old work preserved.", flush=True)
