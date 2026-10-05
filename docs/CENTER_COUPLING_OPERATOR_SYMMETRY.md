# Center coupling: geometric reconstruction and symmetry tests

Base: `e3e8820945072e9140dbcb02e4156af94724432a`.

## Mandatory first test — before any Hardy investigation

The first complete cell has center 4 and physical material edges 2 and 3.
`finitePhysicalCenterInput` places the physical pair into the existing
`FiniteSeedGradientCarrier 4`, with seed and residual edges zero.
`finiteOneCellCenterReconstruction` uses the existing finite prefix preceding
the geometric center. Therefore reconstruction(deltaLeft)=1 and
reconstruction(deltaRight)=0, proved literally in Lean.

The finite self-coupling is reconstructed-center times the two geometric log
gaps. Its matrix in {L0,R0}, in the standard physical Hilbert coordinates, is

```
[ log4-log3   0 ]
[ log5-log4   0 ]
```

`finitePhysicalCenterCoupling_inner_left_right` gives log5-log4;
`finitePhysicalCenterCoupling_inner_right_image` gives zero.
Strict monotonicity of log proves
`finitePhysicalCenterCoupling_not_symmetric`.

This excludes only a symmetric physical diagonal center-coupling block in
this metric. It does not exclude a full completed clock or a larger carrier.
No metric, moments, depth frequency or nodal infinite state is introduced.

## Next steps in this round

Only after this increment is audited/published: define the raw linear center
coupling on seed + material differences, prove its orbit and physical/residual
crosswalks, construct the canonical physical zero-extension, and inspect a
uniform Hardy bound. No boundedness is assumed. If an adequate short Hardy
route is unavailable, stop with `HARDY_CENTER_COUPLING_BOUND_OPEN`.

## Verification

Public names have explicit Analysis guards and `#print axioms`; footprints
are restricted to `[propext, Classical.choice, Quot.sound]` or a subset.
Module/scoped audit/Analysis/Audit builds use `--wfail`; run Analysis,
Foundation and Geometry audits, placeholder scan and `git diff --check`.
