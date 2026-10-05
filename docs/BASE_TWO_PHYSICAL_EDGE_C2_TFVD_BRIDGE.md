# Base-two physical edges to true C2 vertical fibers

Initial main: `d8d45bcd79b7c95bcaa15fc895e3b83f53c6ee29`.

## Address increment

`BaseTwoPhysicalEdgeC2Address` uses `BaseTwoPhysicalEdge = ℕ × Fin 2`.
Side 0 is the existing left cell edge `4k+2`; side 1 is the right edge `4k+3`.
Its range is exactly residues 2 and 3 modulo 4, and it is injective.
The odd endpoints are respectively `4k+3` and `4k+5`. Together they enumerate
all odd material integers at least 3, without duplication. The inverse is
explicit: residue 3 selects `((n-3)/4,0)`, residue 1 selects `((n-5)/4,1)`.
No choice enumerates edges or selects addresses.

The endpoint equivalence is composed with the **existing**
`globalC2BranchAddressEquivOddMaterial.symm`. Thus core, sign and actual depth
come from the already proved material decoder. Both endpoints' selected
neighbor is the original `baseTwoCenter k = 4(k+1)`, and

\[
2^{\operatorname{depth}(a)}\operatorname{core}(a)=4(k+1).
\]

`baseTwoPhysicalEdgeC2Address_center` proves this equality. The direction
agrees with the cell side; left/right legs are center-minus/plus-one. The depth
is the existing neighbor-center factorization crosswalk, never the edge number.
This increment adds no gradient state, metric, moment or physical amplitude.

Every public declaration is guarded/printed in the Analysis audit and the
scoped address audit. Footprint is restricted to
`[propext, Classical.choice, Quot.sound]` and subsets. No historical repository
is imported or needed. Builds use `--wfail`; kernel audit and source scan reject
placeholders and new axioms. The address increment is integrated before work
on the Hilbert restriction and TFVD input begins.

The subsequent seam is the contractive physical restriction of the existing
ordinary/log material-edge vectors, with the residual edges retained. Address
reindexing must precede vertical TFVD. No raw nodal reconstruction is allowed.

## Completed physical/residual Hilbert and TFVD increment

Status: `PASS_BASE_TWO_PHYSICAL_EDGE_C2_TFVD_BRIDGE`.

`BaseTwoPhysicalEdgeTfvdBridge` restricts a complex material-edge ℓ² vector
contractively to the physical edges. It then realifies each complex coordinate
using the existing `Complex.equivRealProdLm`, `realPlaneHilbertEquiv` and
`realPlaneToComplexIsometry` roundtrip. The two real quadratures are preserved.
Only after the proved endpoint/address equivalence does the coordinate become
`(core, direction, j)` with actual C2 depth `j+2`.

`baseTwoPhysicalEdgeC2State` is a continuous **real-linear contraction** into
`GlobalC2BranchCarrier`; no injectivity on all material edges is asserted.
It reads no residual coordinate. Its coordinate law at the address of edge e is

\[
 P(g)(\operatorname{address}(e))
   =\operatorname{realify}(g(\operatorname{edgeIndex}(e))).
\]

This is a gradient-state reindexing, not the physical branch amplitude source
`c2GlobalGreenInputIsometry`. No amplitude is replaced or identified.

### Residual retained, exact standard energy

The physical projection retains residues 2/3 modulo 4. The complementary
projection retains residues 0/1. They reconstruct every material-edge vector,
are orthogonal, and satisfy the exact unweighted identities

\[
 g=P_{\rm phys}g+P_{\rm res}g,
\qquad
 \|g\|^2=\|P(g)\|^2+\|P_{\rm res}g\|^2.
\]

`baseTwoPhysicalResidualC2_injective` proves that the **actual C2 state plus
residual** is lossless, rather than only an abstract pair of masks.
`baseTwoPhysicalEdgeC2State_norm_sq_projection` proves equality of the C2
physical energy and physical projection energy. The proof uses injective
restriction, existing coordinate packaging and exact index reindexing/zero
extension; no weights or new metric are chosen.

### Ordinary/log states, concrete boundary

`baseTwoPhysicalOrdinaryC2State` and `baseTwoPhysicalLogGradientC2State` reuse
exactly the two completed ℓ² vectors from the preceding round. Their coordinate
formulas are the ordinary material gradient and explicit native logarithmic
difference at the corresponding edge index.

`baseTwoCompletedBoundaryValue_eq_physicalChannel` proves that the existing
complete return is the sum of packaged physical right coordinates minus left
coordinates. `summable_baseTwoPhysicalCellReturn` proves absolute convergence
from the already proved whole-cell family. The residual is information retained
outside **this** observable; it is not declared irrelevant or scalarized.
No bounded sum functional on all `GlobalC2BranchCarrier` is constructed.

### Genuine fiber TFVD and clock compatibility

`baseTwoPhysicalOrdinaryTfvd` and `baseTwoPhysicalLogGradientTfvd` apply the
existing `c2FiberTfvdAnalysis`. Their synthesis theorems reuse
`c2FiberTfvdSynthesis_analysis`, preserving all core, direction, quadrature and
vertical labels and the two existing fiber trace/return data.

`baseTwoPhysicalResidualTfvdAnalysis` retains the residual next to the TFVD
output and is injective when `0 < eta < 1`. The concrete
`baseTwoCompletedPhysicalResidualTfvdPair` stores both ordinary/log analyses
and both residual vectors. The critical base-two specialization uses the
**existing derived** `criticalVerticalAmplitudeRatio 2`; it introduces no weight
and does not change either gradient amplitude. Its two synthesis laws are
`baseTwoCriticalPhysicalTfvd_synthesis`.

The full C2 ordinary state is strongly differentiable. Each actual TFVD
core/direction/quadrature channel is a bounded real-linear map, so
`baseTwoPhysicalOrdinaryTfvd_hasDerivAt` gives

\[
 \frac d{dt}\operatorname{TFVD}(P g_t)_{m,a,r}
   =\operatorname{TFVD}(P(-i c_t))_{m,a,r}.
\]

The trace coordinates are included in this norm derivative. The C2 endpoint
label does not make the transported clock multiplication by log(endpoint):
the log-gradient still contains both material frequencies of its edge. Multiplication by
`-i` occurs **before** realification; explicitly it sends the quadrature pair
`(re,im)` to `(im,-re)`. It is not pulled through a real-linear map as if that
map were complex-linear. No global Hilbert norm on the plain function carrier
`C2RealTfvdChannels` is asserted by these per-fiber derivative statements.

### Exact next seam

The material-edge-to-true-C2-fiber input map previously open is now constructed
for the physical channel; its residual is separately retained and the joint
TFVD analysis is lossless. The next seam is a geometrically specified
Green/Naimark realization of this **joint physical TFVD + residual** carrier,
with clock intertwining and its intrinsic symmetry test. Existing standard
product nonsymmetry and nodal no-gos are preserved. Neither symmetry nor
self-adjointness, a canonical moment first column, Hankel or Krylov is claimed.
The total synthesized return is not identified with one of the individual
vertical TFVD traces merely because both are called boundary data.

### Audit and integration

All public declarations in both modules have central and scoped
`#assert_analysis_axioms` / `#print axioms` checks. The permitted footprint is
only `[propext, Classical.choice, Quot.sound]` and subsets; no new axiom,
placeholder or trust escape. Foundation and Geometry are unchanged.

Each increment is built with `--wfail` (module, scoped audit, Analysis,
Analysis.Audit), checked with `lake env lean` on its scoped audit, then audited
with `audit-analysis.sh`, `audit-foundation.sh`, `audit-geometry.sh`, a source
placeholder scan and `git diff --check` before publishing in main.

The address increment is commit
`da5f8a58d2380c95ef56ac8471046ebbc208e8c5`. The containing second increment is
`feat: transport physical material gradients through true C2 fiber TFVD`;
its SHA and final remote equality are reported in the execution report.

Verification result for both increments: all listed builds/audits/kernel checks,
placeholder scans and diff checks completed with exit status zero. All public
capstones satisfy the standard Analysis axiom guard; Foundation remains
empty-footprint and Geometry retains its own stricter discrete guard.
