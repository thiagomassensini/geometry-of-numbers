#!/usr/bin/env python3
"""Rebuild the unchanged source/TFVD ancestors actually imported."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

root = Path(__file__).resolve().parent
repo = root.parents[1]
base = "562e8f8302a84f9ffdb2021384ea7a21f2edb14b"
records = {}
verify_only = "--verify-existing" in sys.argv
prior = json.loads((root / "evidence/upstream.json").read_text())["modules"] if verify_only else {}
schedule = [
    ("all-order-binomial-green", ["ShiftedDifferences", "BinomialCoefficient"]),
    ("native-vertical-synthesis", ["SchurBound", "NativeSynthesis", "Quadratures"]),
    ("native-tfvd-completed-transport", ["ShiftTransport", "PhysicalTfvd", "CoefficientPorts",
                                         "CompletionCommutator", "CompletedSourceBridge"]),
    ("native-commutator-mixed-control", ["NativeWeightLaw", "NullCommutator", "MixedReduction", "NativeJets", "GreenSeed"]),
    ("native-critical-tfvd-cancellation", ["ResponseFlux", "CriticalVectors", "ResponseTaylor", "PhysicalKernels", "SectorExpansion", "Cancellation"]),
    ("native-curvature-green-factor", ["ComplementNorm", "CurvatureKernel", "NativeCoefficient", "FourthBoundaryDefect"]),
    ("native-linear-tfvd-traces", ["FiniteTraces", "PhysicalNumerator", "GreenPairing"]),
    ("native-all-order-stencil-boundary", ["Stencil"]),
    ("native-all-order-spatial-correction", ["DifferencePowers", "DividedKernel", "NativeSpatialLaw", "Regression"]),
    ("native-all-order-energy-correction", ["ResponseExpansion", "PairExpansion", "FiniteEnergy", "RegressionEnergy"]),
    ("native-odd-energy-correction", ["OddProfiles", "OddPairExpansion", "OddFiniteEnergy", "OddRegression"]),
    ("native-even-odd-complete-pairing", ["ResponseReality", "MixedPairing", "JointEnergy", "MixedRegression"]),
    ("native-mixed-imaginary-law", ["MixedSpatialLeading", "MixedRayLeading", "FiniteImaginaryLaw", "ImaginaryRegression"]),
    ("native-cross-radial-complete-pairing", ["CrossRadialPairing", "CrossRadialGreen", "DoubledMixedExpansion", "RadialRegression"]),
    ("native-cross-radial-green-leading", ["PartVectors", "RadialPartExpansion", "LeadingCrossings", "GreenRegression"]),
    ("native-cross-radial-green-cubic", ["PartTaylor", "CubicVectors", "CubicCrossings", "CubicRecomposition"]),
    ("native-odd-green-compensation", ["OddVectors", "OddCompensation", "OddHankelTransport", "OddRegressions"]),
    ("native-cubic-odd-green-defect", ["OddWeights", "CubicOddVectors", "CriticalOddGreen", "CriticalOddDefect"]),
    ("native-all-order-odd-cauchy", ["ComplementRows", "OddCauchyRows", "OddKernelFilters", "AllOrderGreenFilters"]),
    ("native-critical-squared-grid", ["SquaredGrid", "CriticalGridPolynomial", "NativeCriticalGrid", "GridSignObstruction"]),
    ("native-critical-address-split", ["AddressGreen", "OddAddressLowering", "CriticalAddressSplit", "PhysicalPrincipalSplit"]),
    ("native-principal-boundary-flow", ["EndpointFlux", "PrincipalFlux", "NativePrincipalFlux", "FluxObstruction"]),
    ("native-tail-return-graph", ["FiniteReturnDomain", "TailReturnGraph", "PolarizedReturnDefect", "FourSourceBridge"]),
    ("native-four-boundary-margin", ["PhysicalBoundaryCoordinates", "PrincipalBoundaryLimit", "CoercivePhysicalMargin"]),
    ("native-critical-complete-margin", ["CriticalBoundaryTransport", "FourSourcePathLimit", "DefectUniformControl", "CriticalCompleteMargin"]),
    ("native-euler-newton-four", ["ExplicitNewtonInput", "EulerNewtonBridge", "CriticalJetTransport", "TransportedEnergyControl"]),
    ("native-binomial-source-all-order", ["BinomialInverse", "NativeNewtonInput", "CoordinateCoherence", "FullSourceTransport", "AllOrderEnergyControl"]),
    ("native-euler-newton-all-order", ["ShiftedFalling", "EulerNewtonMatrix", "NativeEulerTransport", "MovingEulerLimit", "MatrixCoherence"]),
    ("native-moving-euler-balance", ["UniformMovingError", "MovingBalanceLimit", "PolarizedBoundaryReadout", "MovingPolarizedPair"]),
]
# The input #126 archive adds the unchanged exact-box ancestors and its
# source-response diagnostics. They are verified/rebuilt in dependency order.
for rel in json.loads((root.parent/'native-radial-flow-audit/extra-source-schedule.json').read_text()):
    path=Path(rel)
    schedule.append((path.parts[1],[path.stem]))
schedule.append(('native-radial-flow-audit', ['SourceJets','FlowJets','CayleyFlow','RadialReality',
    'KernelTaylor','RadialDefect','FlowInterval','KernelSign']))
for directory, modules in schedule:
    for module in modules:
        p = root.parent / directory / f"{module}.lean"
        rel = str(p.relative_to(repo))
        original = subprocess.check_output(["git", "show", base + ":" + rel], cwd=repo)
        assert p.read_bytes() == original, rel
        if verify_only:
            assert prior[module]["source_sha256"] == hashlib.sha256(original).hexdigest(), rel
            assert prior[module]["olean_sha256"] == hashlib.sha256((p.parent / ".cache" / f"{module}.olean").read_bytes()).hexdigest(), rel
        else:
            subprocess.run(["bash", "compile_module.sh", module, str(p)], cwd=root, check=True)
        records[module] = {"source": rel, "source_sha256": hashlib.sha256(original).hexdigest(),
            "olean_sha256": hashlib.sha256((p.parent / ".cache" / f"{module}.olean").read_bytes()).hexdigest()}
(root / "evidence").mkdir(exist_ok=True)
(root / "evidence/upstream.json").write_text(json.dumps({"base": base, "modules": records}, indent=2) + "\n")
print("PASS: unchanged source/TFVD ancestors " + ("checked against source/olean hashes from the recorded build." if verify_only else "rebuilt from their exact base."))
