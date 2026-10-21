#!/usr/bin/env python3
"""Reproduce the kernel proofs and audit the unchanged native provenance."""
import gzip
import hashlib
import json
import os
import pathlib
import re
import subprocess
import time
import tempfile

root = pathlib.Path(__file__).resolve().parent
repo = root.parent.parent
operator = repo.parent / "carry-self-adjoint-operator"
evidence = root / "evidence"
evidence.mkdir(exist_ok=True)
env = os.environ.copy()
env["PATH"] = "/home/thlinux/.elan/bin:" + env["PATH"]
base = "aac80d6699009f15de138aa3932b21ab3572ff42"

def read(*args, cwd=repo):
    return subprocess.check_output(args, cwd=cwd, env=env, text=True).strip()

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

protected = [operator / "CarrySelfAdjointOperator" / f for f in
             ["C2OddTfvdTransport.lean", "C2OddTfvdTransportAudit.lean"]]
preflight = {
    "base": base,
    "pr41_commit": "ee56930a2c30456cfbd214a29bb31b12d3977204",
    "pr49_commit": "aac80d6699009f15de138aa3932b21ab3572ff42",
    "protected_refs": {b:read("git","rev-parse",b) for b in ["main","agent/native-moment-orthogonalization-audit","agent/seventh-even-centered-source","agent/native-jet-overlap-budget","agent/source-euler-residual-control"]},
    "branch": read("git", "branch", "--show-current"),
    "head_before_commit": read("git", "rev-parse", "HEAD"),
    "origin_main": read("git", "rev-parse", "origin/main"),
    "operator_head": read("git", "rev-parse", "HEAD", cwd=operator),
    "operator_status": read("git", "status", "--short", cwd=operator),
    "operator_tracked_diff": read("git", "diff", "HEAD", "--", cwd=operator),
    "protected_sha256": {str(p): digest(p) for p in protected},
    "manifest_sha256": digest(repo / "lake-manifest.json"),
    "operator_manifest_sha256": digest(operator / "lake-manifest.json"),
    "toolchain": (repo / "lean-toolchain").read_text().strip(),
    "operator_toolchain": (operator / "lean-toolchain").read_text().strip(),
    "worktrees": read("git", "worktree", "list", "--porcelain"),
}
assert not preflight["operator_tracked_diff"]
(evidence / "preflight.json").write_text(json.dumps(preflight, indent=2) + "\n")
for p in root.glob("*.lean"):
    if re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", p.read_text(), re.M):
        raise RuntimeError(f"Untrusted source token: {p}")
relative = str(root.relative_to(repo))
checks = [
    ("audit-generation", ["python3", f"{relative}/generate_audit.py"], repo),
    ("native-source-build", ["lake", "build", "--wfail",
        "CarrySelfAdjointOperator.NativeCauchyLaguerreShift",
        "CarrySelfAdjointOperator.CompletedNativeChiralReturnEnergyPort",
        "CarrySelfAdjointOperator.C2GlobalGreenBridge"], operator),
    ("pr41-geometry-build", ["lake", "build", "--wfail",
        "GeometryOfNumbers.Analysis.CarryMaterialSourceFactor",
        "GeometryOfNumbers.Analysis.LogarithmicMomentHankel",
        "GeometryOfNumbers.Analysis.CanonicalFiniteHeight"], repo),
    ("pr41-source-build", ["python3", "research/native-jet-overlap-budget/prepare_pr41.py"], repo),
]
checks += [(f"inherited-{m}", ["bash", "research/physical-trace-fiber/compile_module.sh", m], repo)
           for m in ["TraceFiber", "NativeCompletion", "ReadoutTransport"]]
checks += [(f"inherited-native-{m}", ["bash", "research/native-fiber-transport/compile_module.sh", m], repo)
           for m in ["CoherentSplit", "TransportBudget", "SourceSpan", "KernelBudget", "SeparationCorrection", "NativeCauchyOverlap"]]
checks += [(f"pr48-{m}", ["bash", "research/native-jet-overlap-budget/compile_module.sh", m], repo)
           for m in ["OverlapGeometry", "JetBudget", "DampedCamera", "PR41Bridge"]]
checks += [(f"pr49-{m}", ["bash", "research/source-euler-residual-control/compile_module.sh", m], repo)
           for m in ["ResidualEuler", "PolarizedEuler"]]
checks += [(f"kernel-{m}", ["bash", f"{relative}/compile_module.sh", m], repo)
           for m in ["SquareEnergy", "ShiftBoundary", "ShiftMoments", "SourceSquare", "NativeTests", "Audit"]]
checks += [
    ("focused-build", ["lake", "build", "--wfail", "GeometryOfNumbers.Analysis.MomentGramPositivity"], repo),
    ("root-build", ["lake", "build", "--wfail"], repo),
    ("foundation-audit", ["bash", "scripts/audit-foundation.sh"], repo),
    ("geometry-audit", ["bash", "scripts/audit-geometry.sh"], repo),
    ("analysis-audit", ["bash", "scripts/audit-analysis.sh"], repo),
    ("twelve-source-regression", ["bash", "research/sixth-odd-twelve-sources/compile_module.sh", "Regression"], repo),
    ("historical-files-unchanged", ["git", "diff", "--exit-code", base, "--", ".", f":(exclude){relative}"], repo),
    ("diff-check", ["git", "diff", "--check"], repo),
]
results = []
for name, command, cwd in checks:
    started = time.monotonic()
    log = evidence / f"{name}.log"
    # Keep live logs outside the checkout: repository audits run git diff --check.
    with tempfile.TemporaryFile(mode="w+", encoding="utf-8") as output:
        result = subprocess.run(command, cwd=cwd, env=env, stdout=output, stderr=subprocess.STDOUT)
        output.seek(0)
        clean_log = "\n".join(line.rstrip() for line in output.read().splitlines())+"\n"
    log.write_text(clean_log)
    results.append({"name": name, "command": command, "cwd": str(cwd),
                    "exit_code": result.returncode, "seconds": round(time.monotonic()-started, 3)})
    (evidence / "checks.json").write_text(json.dumps(results, indent=2)+"\n")
    print(name + (": PASS" if result.returncode == 0 else ": FAIL"), flush=True)
    if result.returncode:
        print(log.read_text()[-6000:])
        raise SystemExit(result.returncode)
assert read("git", "rev-parse", "origin/main") == preflight["origin_main"]
assert read("git", "rev-parse", "HEAD", cwd=operator) == preflight["operator_head"]
assert read("git", "status", "--short", cwd=operator) == preflight["operator_status"]
assert not read("git", "diff", "HEAD", "--", cwd=operator)
assert digest(repo / "lake-manifest.json") == preflight["manifest_sha256"]
assert digest(operator / "lake-manifest.json") == preflight["operator_manifest_sha256"]
for b,ref in preflight["protected_refs"].items():
    assert read("git","rev-parse",b)==ref
for p in protected:
    assert digest(p) == preflight["protected_sha256"][str(p)]
for p in evidence.glob("*.log"):
    text = "\n".join(line.rstrip() for line in p.read_text().splitlines())+"\n"
    p.write_text(text)
    if p.stem in {"root-build", "analysis-audit"}:
        p.with_suffix(".log.gz").write_bytes(gzip.compress(text.encode(), mtime=0))
        p.unlink()
manifest = {str(p.relative_to(root)): digest(p) for p in sorted(root.iterdir())
            if p.suffix in {".lean", ".py", ".sh"}}
(evidence / "source-sha256.json").write_text(json.dumps(manifest, indent=2)+"\n")
print(f"PASS: {len(results)} checks; inherited PRs, main, pins and native source preserved", flush=True)
