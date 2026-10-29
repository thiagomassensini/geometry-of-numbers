#!/usr/bin/env python3
"""Record unchanged source definitions, dependency pins, base and protected work."""
from pathlib import Path
import hashlib
import json
import subprocess

root = Path(__file__).resolve().parent
repo = root.parents[1]
operator = Path("/home/thlinux/carry-self-adjoint-operator")
momentos = Path("/home/thlinux/momentos")
base = "655e63b4d78aaefe3a442dabf945c2df698d2a59"

def run(args, cwd):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert run(["git", "merge-base", "HEAD", base], repo) == base
sources = {}
for module in ["NativePhysicalGreenResolvent", "NativeIntervalMultiplier",
               "NativeCompletedFiniteGreenResidual", "NativeIncidenceCauchyPorts",
               "CompletedNativeProjectiveChiralCarrier", "CompletedNativeRadialChiralMultiplier",
               "CompletedNativeChiralJetStorageTransport", "CompletedNativeCentralProductDressingAudit"]:
    p = operator / "CarrySelfAdjointOperator" / f"{module}.lean"
    relative = str(p.relative_to(operator))
    assert p.read_bytes() == subprocess.check_output(["git", "show", "HEAD:" + relative], cwd=operator)
    sources[relative] = sha(p)
protected = [operator / "CarrySelfAdjointOperator/C2OddTfvdTransport.lean",
             operator / "CarrySelfAdjointOperator/C2OddTfvdTransportAudit.lean",
             momentos / "AUDITORIA_CORRECTED_MOMENTS_VS_CANONICAL_RECURRENCE.md"]
record = {
    "base": base, "branch": run(["git", "branch", "--show-current"], repo),
    "main": run(["git", "rev-parse", "main"], repo),
    "origin_main": run(["git", "rev-parse", "origin/main"], repo),
    "operator_head": run(["git", "rev-parse", "HEAD"], operator),
    "operator_status": run(["git", "status", "--porcelain=v1"], operator),
    "momentos_status": run(["git", "status", "--porcelain=v1"], momentos),
    "source_sha256": sources,
    "protected_sha256": {str(p): sha(p) for p in protected},
    "pins": {p: run(["git", "rev-parse", "HEAD"], operator / ".lake/packages" / p)
             for p in ["CPFormal", "NativeCarryC3Crosswalk", "NativeCarrySpectralWeyl"]},
    "native_tower_source_sha256": sha(operator / ".lake/packages/CPFormal/CPFormal/Analytic/CpNativeGpreTowerNorm.lean"),
    "pr93": json.loads(run(["gh", "pr", "view", "93", "--repo", "thiagomassensini/geometry-of-numbers",
                            "--json", "state,isDraft,headRefOid,baseRefName"], repo)),
}
geometry_sources = {}
for module in ["RealCarryTfvd", "RealCarryL2", "RealCarryWeightedValve", "RealCarryGreenKernel"]:
    path = repo / "GeometryOfNumbers/Analysis" / f"{module}.lean"
    relative = str(path.relative_to(repo))
    assert path.read_bytes() == subprocess.check_output(["git", "show", base + ":" + relative], cwd=repo)
    geometry_sources[relative] = sha(path)
record["geometry_tfvd_sources_sha256"] = geometry_sources
(root / "evidence").mkdir(exist_ok=True)
(root / "evidence/source-provenance.json").write_text(json.dumps(record, indent=2) + "\n")
print("PASS: original native tower, Cauchy source, completed return, base and pins recorded.")
