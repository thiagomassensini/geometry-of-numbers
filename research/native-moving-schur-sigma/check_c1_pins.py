#!/usr/bin/env python3
"""Check every reachable non-Mathlib source import used by the C1 build."""

from __future__ import annotations

import os
import pathlib
import re
import subprocess
import sys


REPO = pathlib.Path(__file__).resolve().parents[2]
CARRY = pathlib.Path(
    os.environ.get("CARRY_LEAN_ROOT", "/home/thlinux/carry-self-adjoint-operator")
).resolve()
GEOMETRY_PIN = "2a3e89987beeb05d29b2e71d8b8ed6851383ccaa"
CARRY_PIN = "045369f6dedcb2e75e9aefed1d12c9f73b9a2532"


def git(root: pathlib.Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def require_head(root: pathlib.Path, expected: str) -> None:
    actual = git(root, "rev-parse", "HEAD")
    if actual != expected:
        raise RuntimeError(f"{root} HEAD {actual} does not match pinned revision {expected}")


def imports(path: pathlib.Path) -> list[str]:
    found: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"^\s*import\s+(.+?)\s*$", line)
        if match:
            found.extend(re.findall(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", match.group(1)))
    return found


def main() -> int:
    package_specs = {
        "CarrySelfAdjointOperator": (CARRY, CARRY_PIN, False),
        "CPFormal": (CARRY / ".lake/packages/CPFormal", "65d50f6db1208708e109982ba97e1d51d3039956", True),
        "NativeCarrySpectralWeyl": (CARRY / ".lake/packages/NativeCarrySpectralWeyl", "298d83c9351e308a5213b9f5ac32e44087f98a9f", True),
        "GreenFrame": (REPO / ".lake/packages/GreenFrame", "cd2d838bee67ad23f869a02f8ed9f0a0feb926fa", True),
        "GeometryOfNumbers": (REPO, GEOMETRY_PIN, False),
        "NativeCarryC3Crosswalk": (CARRY / ".lake/packages/NativeCarryC3Crosswalk", "150cfc7fb08da96bf8117f15869cc2b819d593c2", True),
        "FiniteNativeCarryOperator": (CARRY / ".lake/packages/FiniteNativeCarryOperator", "00e9d6beb17226545abf5ddf90bbfede6c7146b0", True),
    }
    for root, pin, check_head in package_specs.values():
        if check_head:
            require_head(root, pin)
    seed_files = [
        "research/native-moving-schur-sigma/MomentComplexification.lean",
        "research/native-moving-schur-sigma/MomentLogConvexity.lean",
        "research/native-moving-schur-sigma/SigmaZeroObstruction.lean",
        "research/native-moving-schur-sigma/SigmaNativeContinuation.lean",
        "research/native-moving-schur-sigma/SigmaNativeZeroBridge.lean",
        "research/native-moving-schur-sigma/SigmaCertifiedNegativeDirection.lean",
        "research/native-sixth-explicit-sigma/SigmaParity.lean",
        "research/native-sixth-explicit-sigma/SigmaCenterZero.lean",
        "research/native-sixth-explicit-sigma/SigmaCenterAll.lean",
        "research/native-sixth-explicit-sigma/SigmaGreenCurvature.lean",
        "research/native-sixth-explicit-sigma/SigmaOffcenter.lean",
        "research/native-sixth-explicit-sigma/SigmaOffcenterBridge.lean",
        "research/native-sixth-explicit-sigma/SigmaCurvature.lean",
        "research/native-sixth-explicit-sigma/SigmaQuadratic.lean",
        "research/native-moving-schur-sigma/MatrixJetCalculus.lean",
        "research/native-moving-schur-sigma/SigmaNeighborhood.lean",
        "research/native-moment-orthogonalization-audit/MomentFunctional.lean",
        "research/native-moment-orthogonalization-audit/JacobiLogic.lean",
        "research/native-moment-orthogonalization-audit/PolynomialCoordinates.lean",
        "research/native-moment-orthogonalization-audit/NativeApplication.lean",
        "research/native-moment-orthogonalization-audit/SchurLogic.lean",
    ]
    queue: list[str] = []
    for rel in seed_files:
        source = REPO / rel
        if not source.is_file():
            raise RuntimeError(f"missing C1 build source: {rel}")
        queue.extend(imports(source))

    prefixes = sorted(package_specs, key=len, reverse=True)
    checked: set[str] = set()
    counts = {prefix: 0 for prefix in package_specs}
    failures: list[str] = []
    while queue:
        module = queue.pop()
        if module in checked:
            continue
        checked.add(module)
        prefix = next(
            (candidate for candidate in prefixes if module == candidate or module.startswith(candidate + ".")),
            None,
        )
        if prefix is None:
            continue
        root, pin, _ = package_specs[prefix]
        rel = module.replace(".", "/") + ".lean"
        source = root / rel
        if not source.is_file():
            failures.append(f"missing source: {module} ({source})")
            continue
        try:
            expected = subprocess.check_output(
                ["git", "-C", str(root), "show", f"{pin}:{rel}"], stderr=subprocess.DEVNULL
            )
        except subprocess.CalledProcessError:
            failures.append(f"source absent at pin {pin}: {module}")
            continue
        if expected != source.read_bytes():
            failures.append(f"source differs from pin {pin}: {module}")
            continue
        counts[prefix] += 1
        queue.extend(imports(source))

    if failures:
        for failure in failures:
            print(f"FAIL: {failure}")
        return 1
    total = sum(counts.values())
    print(f"Geometry base pin: {GEOMETRY_PIN}")
    print(f"Carry main source pin: {CARRY_PIN}")
    for prefix, count in counts.items():
        if count:
            print(f"{prefix}: {count} transitive source modules match their pin")
    print(f"Passed: {total} reachable non-Mathlib source modules match pinned revisions.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"C1 pin audit failed: {error}", file=sys.stderr)
        sys.exit(1)
