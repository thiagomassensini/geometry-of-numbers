#!/usr/bin/env python3
"""Focused Lean checks, type/body axioms, native regressions and preservation."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time

root = Path(__file__).resolve().parent
repo = root.parent.parent
operator = Path("/home/thlinux/carry-self-adjoint-operator")
evidence = root / "evidence"
evidence.mkdir(exist_ok=True)
base = "a236b218f3e68a8fbf714902de196f7234faeaf3"
relative = str(root.relative_to(repo))
env = os.environ.copy()
env["PATH"] = "/home/thlinux/.elan/bin:" + env["PATH"]
env["PYTHONDONTWRITEBYTECODE"] = "1"

def read(*args, cwd=repo):
    return subprocess.check_output(args, cwd=cwd, env=env, text=True).strip()

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

refs = ["main", "origin/main", "agent/c3-fourteenth-tail",
        "agent/native-moment-orthogonalization-audit"]
protected = [operator / "CarrySelfAdjointOperator" / name for name in
             ["C2OddTfvdTransport.lean", "C2OddTfvdTransportAudit.lean"]]
manifests = [repo / "lake-manifest.json", operator / "lake-manifest.json"]
preflight = dict(base=base, branch=read("git", "branch", "--show-current"),
    head_before_commit=read("git", "rev-parse", "HEAD"),
    protected_refs={r: read("git", "rev-parse", r) for r in refs},
    operator_head=read("git", "rev-parse", "HEAD", cwd=operator),
    operator_status=read("git", "status", "--short", cwd=operator),
    protected_source_sha256={str(p): sha(p) for p in protected},
    manifest_sha256={str(p): sha(p) for p in manifests},
    worktrees=read("git", "worktree", "list", "--porcelain"),
    toolchain=(repo / "lean-toolchain").read_text().strip(),
    environment="minimal original operator lake env; no main project library override")
prior = repo / "research/entrywise-moment-square"
preflight["preserved_untracked"] = {str(p.relative_to(prior)): sha(p)
    for p in sorted(prior.rglob("*")) if p.is_file()}
(evidence / "preflight.json").write_text(json.dumps(preflight, indent=2) + "\n")
for p in root.glob("*.lean"):
    if re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", p.read_text(), re.M):
        raise RuntimeError("Forbidden source token: " + str(p))
read("git", "diff", "--exit-code", "HEAD", "--", cwd=operator)

modules = ["SourceBezout", "SourceMap", "SourceNative", "SourceBlocks", "SchurTransport",
           "SourceSchur", "LiteralNativeTrace", "LiteralTfvd", "KernelBudget",
           "LiteralTailBounds", "LiteralBudgetLimit", "LiteralCompanion", "CompanionJets", "Repartition",
           "Regression", "Audit"]
checks = [("audit-generation", ["python3", relative + "/generate_audit.py"], repo)]
checks += [("kernel-" + m, ["/usr/bin/time", "-v", "bash", relative + "/compile_module.sh", m], repo)
           for m in modules]
checks += [
    ("literal-diagnostic", [os.environ.get("CARRY_DIAGNOSTIC_PYTHON", "/home/thlinux/miniforge3/bin/python"), relative + "/diagnose_literal_terms.py"], repo),
    ("focused-build", ["lake", "build", "--wfail",
        "GeometryOfNumbers.Analysis.CarryMaterialProjectiveReturnGreen",
        "GeometryOfNumbers.Analysis.CarryMaterialCompanionGreenTransport",
        "GeometryOfNumbers.Analysis.CanonicalFiniteHeight"], repo),
    ("root-build", ["lake", "build", "--wfail"], repo),
    ("foundation-audit", ["bash", "scripts/audit-foundation.sh"], repo),
    ("geometry-audit", ["bash", "scripts/audit-geometry.sh"], repo),
    ("analysis-audit", ["bash", "scripts/audit-analysis.sh"], repo),
    ("twelve-source-regression", ["bash", "research/sixth-odd-twelve-sources/compile_module.sh", "Regression"], repo),
    ("historical-files-unchanged", ["git", "diff", "--exit-code", base, "--", ".", ":(exclude)" + relative], repo),
    ("diff-check", ["git", "diff", "--check"], repo),
]
parser = argparse.ArgumentParser()
parser.add_argument("--resume", action="store_true", help="Reuse unchanged successful module builds")
args = parser.parse_args()
previous = {r["name"]: r for r in json.loads((evidence / "checks.json").read_text())} if args.resume else {}
results = []
for name, command, cwd in checks:
    old = previous.get(name)
    if old and old["exit_code"] == 0 and name.startswith("kernel-") and name != "kernel-Audit":
        module = name.removeprefix("kernel-")
        output_file = root / ".cache" / (module + ".olean")
        source_file = root / (module + ".lean")
        if output_file.exists() and output_file.stat().st_mtime >= source_file.stat().st_mtime:
            results.append(old)
            print(name + ": PASS (unchanged compiled source)", flush=True)
            continue
    start = time.monotonic()
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as output:
        result = subprocess.run(command, cwd=cwd, env=env, stdout=output, stderr=subprocess.STDOUT)
        output.seek(0)
        log = "\n".join(line.rstrip() for line in output.read().splitlines()) + "\n"
    if name in ("root-build", "analysis-audit"):
        (evidence / (name + ".log.gz")).write_bytes(gzip.compress(log.encode(), mtime=0))
    else:
        (evidence / (name + ".log")).write_text(log)
    item = dict(name=name, command=command, cwd=str(cwd), exit_code=result.returncode,
                seconds=round(time.monotonic() - start, 3))
    peak = re.search(r"Maximum resident set size \(kbytes\): (\d+)", log)
    if peak: item["maximum_rss_kbytes"] = int(peak.group(1))
    results.append(item)
    (evidence / "checks.json").write_text(json.dumps(results, indent=2) + "\n")
    print(name + (": PASS" if result.returncode == 0 else ": FAIL"), flush=True)
    if result.returncode:
        print(log[-8000:])
        raise SystemExit(result.returncode)
for r, value in preflight["protected_refs"].items():
    assert read("git", "rev-parse", r) == value
assert read("git", "rev-parse", "HEAD", cwd=operator) == preflight["operator_head"]
assert read("git", "status", "--short", cwd=operator) == preflight["operator_status"]
read("git", "diff", "--exit-code", "HEAD", "--", cwd=operator)
assert read("git", "worktree", "list", "--porcelain") == preflight["worktrees"]
for group in ("protected_source_sha256", "manifest_sha256"):
    for p, value in preflight[group].items(): assert sha(Path(p)) == value
for name, value in preflight["preserved_untracked"].items(): assert sha(prior / name) == value
manifest = {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob("*"))
    if p.is_file() and ".cache" not in p.parts and "__pycache__" not in p.parts
    and "evidence" not in p.parts}
(evidence / "source-sha256.json").write_text(json.dumps(manifest, indent=2) + "\n")
print("PASS: " + str(len(results)) + " checks; original source, pins, main, prior branch refs and untracked research preserved", flush=True)
