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
