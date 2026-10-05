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
