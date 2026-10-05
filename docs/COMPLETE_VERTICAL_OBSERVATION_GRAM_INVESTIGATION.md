# Complete vertical observation and canonical Hankel: a directed test

Initial main: `990532835ca40e430772a917d8a63f9702e0cb68` (pulled and clean).

## Question and tested carrier

Can complete vertical observation, reconstruction and independence identify the
canonical Hankel, rather than merely prove positivity of an independent Gram?

The first candidate is the **existing full real TFVD analysis of one genuine C2
vertical fiber**. Its minimal existing R2 interface retains the interior bracket
and two boundary values. `CompleteVerticalObservationCarrier` packages these as

```text
WithLp 2 (CarryVerticalL2 × WithLp 2 (Real × Real)).
```

This is the standard Hilbert product. No new weight, amplitude or scalar moment
enters it. The observer `completeVerticalObservation eta` has components

```text
bracket(x)(0)   = 0
bracket(x)(n+1) = eta^-1*x(n+2) - 2*x(n+1) + eta*x(n)
trace(x)       = (x(0), eta^-1*x(1)-x(0)).
```

The trace retains the initial value and initial weighted slope/flow. Causal
Green plus the affine boundary return reconstructs **the entire fiber**, before
any scalar readout. This experiment takes inner products of all observed
channels together. It does not first reconstruct the coordinate incidence and
then take its original orthogonal Gram. Consequently the old no-go for bare
incidence/isometric reconstruction is preserved and is not used as a shortcut
for this test.

`completeVerticalObservationJet_c2_provenance` identifies these probes with
actual core-1, left-direction, first-quadrature incidences, through
`c2BranchVerticalCoordinate`. The index is the already defined C2 depth-from-two.
No consecutive material edge is relabeled as a depth.

The finite observer `completeVerticalPrefixObservation eta N` observes a
linear combination of the first N such vertical probes. Its input is finite
dimensional; its image lies in their finite-dimensional observed span. No
infinite truncation/limit or new density assumption is required.

## Kernel-checked causal order

1. `completeVerticalObservation_reconstruction` reuses
   `realCarryTfvdSynthesis_comp_analysis`, including both boundary coordinates.
2. `completeVerticalObservation_injective` follows from that left inverse.
3. `completeVerticalObservationJet_linearIndependent` transports independence
   through this injective observer, not through any Hankel assumption.
4. `completeVerticalPrefixObservation_injective` is the finite separating map.
5. `completeVerticalObservabilityGram_posDef` proves its **own** Gram positive
   definite for every N, using the same family's independent prefixes.
6. Only afterward are the exact low entries compared with the index-sum law.

This proves `PASS_GEOMETRIC_OBSERVABILITY_GRAM_POSDEF` for this observation.
It does not prove canonical Hankel positivity.

## Exact finite comparison: already impossible at order three

For J_n = completeVerticalObservation eta (delta_n), all trace components are
still present. The kernel proves

```text
< J_0,J_0 > = eta^2 + 2
< J_0,J_1 > = -2*eta - eta^-1
< J_0,J_2 > = 1                         (eta != 0)
< J_1,J_1 > = 4 + eta^2 + eta^-2.
```

A Hankel requires the last two entries to be the same h_2. Their difference is
`3 + eta^2 + eta^-2 > 0`, independently of any moment values. This is an exact
kernel proof, not a numerical check or normalization adjustment.

`completeVerticalObservabilityGram_not_hankel` excludes equality with
`hankelGram moments 3` for **any** moments. The theorem
`completeVerticalObservationJet_not_momentGram` excludes its all-order moment
representation. `completeCriticalVerticalObservabilityGram_not_canonicalHankel`
specializes to the previously derived critical base-two vertical ratio and the
concrete `baseTwoCanonicalMomentSequence`.

**Status of this candidate: `NO_GO_FULL_TFVD_CHANNEL_GRAM_HANKEL`.**

No odd/mixed construction is added after this necessary even-block test fails.
The canonical moment sequence is used only as a comparison target in the final
specialization. A failed fully retained fiber-channel Gram is a no-go for this
representation and metric; it is not a no-go for the complete theory or for
positivity of the canonical Hankel.

## Inventory and remaining scope

The current repository already retains more data in the material route:
`baseTwoPhysicalResidualTfvdAnalysis` is injective and retains the residual
next to the actual physical C2 channels. Its ordinary/log pair is already
constructed. Seeded gradient, clock and completed boundary states also exist.
These are not identified here with this single fiber, nor with canonical jets.
The observed fiber is complete for its input; it is not advertised as the full
completed/dressed material observable.

Incoming normalized center reconstruction T and outgoing leg synthesis S are
bounded existing maps, with K=S T. `T_phys != S.adjoint` and nonsymmetry of
`naivePhysicalCenterBlock` remain intact. These distinct roles are not collapsed
or replaced by each other in this experiment.

The smallest obstruction for the **tested observer** is literally

```text
inner Real (completeVerticalObservationJet eta 0)
           (completeVerticalObservationJet eta 2)
!=
inner Real (completeVerticalObservationJet eta 1)
           (completeVerticalObservationJet eta 1).
```

This is refuted equality, not an open calibration gate. Changing h_2 cannot
repair it. The more general theory still requires a genuinely different
completed geometric family and an independently established moment readout.
Independence of the present probes cannot be assigned to that future family.
No new symmetric clock is inferred from injectivity or norm positivity; the
Krylov route is not applied to this observer. CanonicalFiniteHeight and its
PosDef premises are not changed.

## Provenance audit

All new objects use only `RealCarryTfvd`, `C2RealFiberTfvdIncidence`, standard
WithLp products and Mathlib Gram/linear-independence APIs. They precede and are
independent of moments and heights. Boundedness is inherited by continuous
linear composition of the existing bracket/trace and standard product charts.
No historical repository or positivity theorem is imported. No C2 amplitude is
identified with material n^-1/2. Seed/flow of the tested fiber remain vector
coordinates; no scalar response is embedded into a one-dimensional carrier.

## Validation

All public names are guarded and printed in Analysis/Audit and the scoped
CompleteVerticalObservationGramAudit. Allowed transitive axioms are only
`[propext, Classical.choice, Quot.sound]` (or a subset). Foundation is untouched.

Commands for this increment:

```bash
lake build --wfail GeometryOfNumbers.Analysis.CompleteVerticalObservationGram \
  GeometryOfNumbers.Analysis.CompleteVerticalObservationGramAudit \
  GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit
bash scripts/audit-analysis.sh
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
git diff --check
git diff --cached --check
```

Validation: all listed builds and three audit scripts exited 0. Placeholder scan
and both unstaged/staged diff checks passed. Capstones print only propext,
Classical.choice and Quot.sound; Foundation keeps an empty footprint.
Commit message: audit: test complete vertical observation Gram before compression.
The integrated SHA is recorded in the delivery report. No canonical moment
Gram/PosDef or sufficiency/minimality of a larger carrier is claimed.

## Second increment: distinct incoming/outgoing center roles

The first increment was integrated at
`b221721ffd98e6172097799cec29c9497c236e88` before starting this construction.

The existing maps have types

```text
T = baseTwoPhysicalCenterReconstruction : PhysicalEdgeL2 ->L CenterL2
S = baseTwoCenterLegSynthesis           : CenterL2 ->li PhysicalEdgeL2.
```

`SeparatedCenterObservation` tests the permitted standard product
`PhysicalEdgeL2 + Center_in + Center_out` (nested WithLp 2 products). These are
copies of existing Hilbert spaces, with no new component norm or coefficient.
The complex-linear packaging reuses the existing complex physical and center
maps; the preceding TFVD test remains real. No scalar response is used as a
Hilbert vector.

The bounded block is exactly

$$A(p,c_{in},c_{out})=(T^\dagger c_{in}+S c_{out},\;T p,\;S^\dagger p).$$

`baseTwoSeparatedCenterBlock_symmetric` proves symmetry from the standard
adjoint identities. Each adjoint accompanies **its own** map. It does not
identify T with S.adjoint, and does not revive the excluded single-center
block. Boundedness comes from composition/products/sums of existing bounded
maps and their standard adjoints. The certified Hardy result is reused, not
proved again.

`baseTwoCenterRoleObservation` keeps (T p,S.adjoint p) as two vector coordinates.
`baseTwoSeparatedCenterBlock_physical` gives A(p,0,0)=(0,T p,S.adjoint p).
`baseTwoCenterRoleObservation_energy` proves the exact sum of their squared
norms. This role observation has **not** been proved injective in this round;
no PosDef claim is made for its Gram. The all-order own PosDef result above
belongs to the separately proved injective full TFVD observer.

`baseTwoSeparatedCenterKrylov_inner_add` specializes the existing abstract
symmetric-Krylov theorem to this block. Hence, for any v in this standard
product, its powers have the index-sum property. The explicit conditional
`baseTwoSeparatedCenter_firstColumn_implies_evenKernel` says

```text
IF for every r:
  baseTwoCanonicalMomentSequence r
    = Re inner Complex v ((A^(2*r)) v)
THEN for every i,j:
  baseTwoCanonicalMomentSequence (i+j)
    = Re inner Complex ((A^(2*i)) v) ((A^(2*j)) v).
```

This conditional is a reduction, not a proved calibration. No v_completed is
constructed from moments or designated by this theorem. No independently
verified canonical first column is supplied. Nor is A identified with the
transported completed material clock: it is the bounded **center-role block**,
without the unbounded material diagonal or the full seed/residual/boundary
source. A symmetric organization of the coupling maps does not establish a
clock intertwining for the actual completed orbit.

Consequently this candidate still requires a provenance-correct completed seed
in this carrier (or an enlargement retaining the other material channels),
independent clock/readout identification and the displayed first-column
calibration. Independence of its Krylov prefixes and mixed-parity orthogonality
are also unproved. It would be inaccurate to report all remaining work as one
scalar equality while no such completed seed/clock realization has been
identified. The theorem isolates the exact **algebraic even-kernel** seam once
that realization exists.

No minimality/sufficiency of two centers for the full theory is claimed. What
is closed is the much narrower test: the two existing distinct roles can occupy
separate adjoint blocks and give a bounded symmetric operator in the unchanged
standard metric.

## Final conclusion of this investigation

- CLOSED: full TFVD observer is separating; its same-family Gram is PosDef.
- REFUTED: its full channel Gram equals a canonical (or any) index-sum Hankel.
  The first structural collision is exactly (0,2) versus (1,1).
- CLOSED: distinct incoming/outgoing center maps admit the explicit symmetric
  bounded block above, and its powers obey the generic Krylov index-sum law.
- OPEN: completed-state/clock provenance and canonical first column for that
  new block; same-family independence and full parity moment Gram.

Main status: `NO_GO_FULL_TFVD_CHANNEL_GRAM_HANKEL`, strictly representation-specific.
Additional result: `PASS_SEPARATED_CENTER_BLOCK_SYMMETRY`.
There is no `PASS_CANONICAL_HANKEL_POSDEF` and no change to Jacobi/finite-height
assumptions. Complete geometric observability gives formal support to positivity
of its own Gram; it does not close the canonical-moment seam. Neither result
refutes the complete theory.

Second increment: SeparatedCenterObservation/scoped audit/Analysis/Analysis.Audit
--wfail builds and Analysis/Foundation/Geometry scripts all exited 0. Public
names pass #assert_analysis_axioms and print only [propext, Classical.choice,
Quot.sound]. Placeholder scan and unstaged/staged diff checks pass. Commit
message: feat: separate geometric incoming and outgoing center adjoint blocks.
The integrated SHA and remote equality are recorded in the delivery report.
