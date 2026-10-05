# Physical center-clock defect

Base checkpoint: `cae0dc65a369518b7583ef51cc74a16d2a6e8a38`.

The ordinary coordinate is a consecutive material difference. Its true clock
uses both material endpoints. The diagonal odd-endpoint clock omits a center
term. This term is defined by subtraction, before any formula simplification.

For center c = baseTwoCenter k the exact identities are:

- left: `(log c - log(c-1)) * criticalMaterialSample t c`;
- right: `(log(c+1) - log c) * criticalMaterialSample t c`.

`baseTwoPhysicalCenterClockDefect_decoded_center` identifies this center with
`baseTwoPhysicalEdgeC2Address_center`; no edge index is interpreted as depth.

## Local energy and packaging

`baseTwoPhysicalCenterClockDefect_norm_le` proves the sufficient bound
`norm(defect(k,side)) <= 1/(k+1)`. It uses `log(1+1/n) <= 1/n` and sample norm
at most one. The squared majorant is a convergent p-series. Thus
`baseTwoPhysicalCenterClockDefect_memℓp` and the L2/C2 states require no new
hypothesis. Realification uses both existing real quadratures and the same
physical-edge/C2-address equivalence.

Public declarations are registered in Analysis/Audit and the scoped audit.
All guards allow only `[propext, Classical.choice, Quot.sound]` (or a subset).

Commands: module/scoped audit/Analysis/Analysis.Audit `lake build --wfail`,
`lake env lean` scoped audit, Analysis/Foundation/Geometry scripts,
placeholder scan and `git diff --check`.

## Remaining increment

Prove the odd-material generator domain from the L2 difference
log-gradient minus center defect, transport the identity through canonical
Parseval, and inspect the unchanged pre-stencil components. No self-adjointness
of the completed transported clock follows from this local correction.
Global boundedness of center coupling and a larger symmetric block realization
are separate gates. No moment, Hankel, Krylov or new metric enters this round.

## Exact Green/Parseval generator transport

The first local energy increment was published as
`963e1ecaa91f0b786669af98f230192cf5f7bd1f`.

`baseTwoPhysicalOddEndpointDiagonalClock` is literally multiplication by
`log(globalC2MaterialAddress)`. Its membership is certified by the C2 difference
log-gradient minus center defect, not assumed. The existing real incidence and
odd-material inclusion compose to `baseTwoPhysicalC2GreenIsometry`, preserving
norm, exact endpoints and both quadratures. This is not the physical-amplitude
source isometry.

`baseTwoPhysicalOrdinaryGreenState_mem_domain` is unconditional for this
concrete gradient orbit. `baseTwoPhysicalClock_Green_generator_decomposition`
proves `logGradientGreen = A ordinaryGreen + defectGreen` with the exact
maximal-domain proof. The existing ambient operator intertwining then gives
`baseTwoPhysicalClock_Parseval_decomposition` and its Parseval domain proof.
No generator, inverse square root, or ambient operator is changed.

`baseTwoCenterSample_eq_seed_physical_residual_prefix` reconstructs the central
sample from seed and both finite material-edge prefixes. Residual edges are
retained. There is no global nodal L2 reconstruction.

Status of this increment: `PASS_PHYSICAL_CENTER_CLOCK_DEFECT_PARSEVAL`.
Pre-stencil sector localization remains a separate test in this round.
`CENTER_DEFECT_BOUNDED_OPERATOR_OPEN`: no Hardy operator bound is claimed.
A larger symmetric block clock still requires the geometric center-coupling
block and its matching adjoint; the identity above does not prove symmetry of
the completed transported clock.
