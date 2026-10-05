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

## Raw geometric coupling and physical zero-extension

The mandatory finite test was integrated and pushed before this investigation
as `af7f4549af244de7603c15ecd31ce820f2a987e3`.

`BaseTwoSeededMaterialHilbert = WithLp 2 (Complex × MaterialEdgeL2)` uses the
standard product Hilbert norm and no independent boundary coordinate.
`baseTwoCenterReconstruction` is a complex-linear map into raw `Nat -> Complex`:
seed plus the finite prefix preceding the existing center. No l2 membership
of these center coordinates is claimed.

`baseTwoCenterCouplingRaw` applies the original left/right logarithmic gaps.
It mentions no orbit or moments. The orbit follows afterward:

- `baseTwoCenterReconstruction_concrete` recovers the actual center sample;
- `baseTwoCenterCouplingRaw_concrete` equals the existing center-clock defect;
- `baseTwoCenterCouplingRaw_seed_physical_residual` retains all three pieces.

`baseTwoPhysicalEdgeEmbedding` is a complex-linear isometric zero-extension
along the existing injective physical edge index. Its two roundtrips are
`baseTwoPhysicalEdgeRestriction_embedding` and
`baseTwoPhysicalEdgeEmbedding_restriction` (the latter equals the physical
projection). No weights or new metric are used.

`baseTwoPhysicalCenterSelfCouplingRaw_first_cell` shows that the global raw
formula has exactly the previously proved first-cell matrix. The two existing
l2 delta witnesses are defined independently, and the deltaLeft/deltaRight
first-cell theorems explicitly recover the two columns.

## Credit guard: exact remaining Hardy gate

Final status: `PASS_FINITE_CENTER_COUPLING_NONSYMMETRY_HARDY_OPEN`.

Directed searches of current Mathlib Analysis and the local Analysis/GreenFrame
modules found Cesaro limit theorems, but no adequate discrete l2 Hardy or
uniform prefix-sum operator bound to instantiate. This is an API/proof gate,
not a theorem that boundedness fails. A new discrete Hardy/Schur estimate would
be required; the credit guard stops this round before that infrastructure.

The precise missing statement, using the already defined raw map, is:

```
exists C >= 0, forall y N,
  sum k < N (‖K_raw y (k,0)‖^2 + ‖K_raw y (k,1)‖^2)
    <= C * ‖y‖^2
```

The constant must be independent of N and valid for arbitrary seeded l2
material inputs. The old orbit bound |sample(c)| <= 1 does not prove this.
No uniform bound, full bounded center coupling, global bounded K_pp,
K_paux adjoint, or infinite naive adjoint block is declared.

## Next structural test

First close the uniform Hardy bound and bounded realization. Then the finite
physical witness must be transported to the global physical operator. An
auxiliary adjoint cannot be presumed to repair that physical diagonal; the
naive block still requires its own theorem. A future center-sector factorization
(reconstruction followed by left/right log-gap synthesis) is only a proposed
investigation, with its domain/norm requirements explicit. No center-sector
l2 state, dilation, Naimark, Krylov or moment construction is made here.

All new public names are kernel checked and guarded. Builds `--wfail` include
both new modules, scoped audits, Analysis and Analysis.Audit; Analysis,
Foundation and Geometry scripts, placeholder scans and `git diff --check`
pass. Allowed capstone axioms: `[propext, Classical.choice, Quot.sound]` or a
subset. The second increment is identifiable by commit message
`feat: derive raw geometric center coupling and physical zero-extension`.
