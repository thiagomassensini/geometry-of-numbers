# Completed signal: raw ℓ² obstruction and boundary inventory

Date: 2026-10-04. Initial main:
`b5c83128d686868adb59c5d47ff4aae7d9b33652`.

## Question and current status

`NO_GO_RAW_L2_COMPLETED_SIGNAL_READOUT` is proved for the raw extension.
This is a no-go of that representation, not of completed boundary geometry.
The ℓ¹ signal lift remains valid; no moment, Hankel, positivity or fitted
weight is used. A geometrically derived Hilbert boundary realization is not
supplied by the current local TFVD APIs.

## Exact raw obstruction

`BaseTwoRawL2ReadoutObstruction.lean` derives signed edges from the existing
base-two cell, and defines the coefficient sequence

```text
c(n) = -1 if n mod 4 = 2;
       +1 if n mod 4 = 3;
        0 otherwise.
```

`baseTwoCompletedUndressedReadout_single` proves this is literally the
previous seeded ℓ¹ readout on `(0, delta_n)`, not a second readout chosen for
the test. The finite-support witness `baseTwoRawL2Witness N` is -1 on
`baseTwoCellLeftEdge k` and +1 on `baseTwoCellRightEdge k`, for `k<N`,
and zero elsewhere. Signed edge injectivity proves there are no collisions.

The kernel proves:

- `baseTwoRawL2Witness_signedEdge`: the exact witness coordinates;
- `baseTwoRawL2Witness_norm_sq`: norm squared is `2*N`;
- `baseTwoRawL2Witness_norm`: norm is `sqrt(2*N)`;
- `baseTwoRawL2Witness_readout`: any linear extension agreeing on deltas
  must give `2*N`;
- `baseTwoRawL2Readout_not_exists`: operator norm would force
  `(2*N)^2 ≤ ‖R‖²*(2*N)` for every N, contradicted by an explicit
  Archimedean choice `N>‖R‖²+1`;
- `baseTwoCompletedReadout_no_rawL2_extension`: directly formulated using
  the previous ℓ¹ readout, even on finite-support coordinate deltas;
- `baseTwoRawL2_no_bounded_boundary_factorization`: for every normed complex
  space E, no bounded `T : MaterialEdgeL2 →L[ℂ] E` and bounded
  `beta : E →L[ℂ] ℂ` can agree with those coefficients on all deltas.

The last statement follows by composition, not by a new assumption about
Green or TFVD. It applies only when the full transform is bounded on **raw
material ℓ²** and agrees on **all finite supports**. It does not rule out a
transform from the stronger ℓ¹ source, a restricted source orbit, or separately
derived boundary data. In particular it does not assert that S(t) cannot be
read in any Hilbert representation.

## Local boundary inventory

| Object | Actual type/data | Bounded? | Relation to present material readout |
|---|---|---|---|
| `carryWeightedVerticalTrace eta` | `CarryVerticalL2 →L[ℝ] (ℝ×ℝ)`; `(x(0), eta⁻¹*x(1)-x(0))` | Yes, coordinate evaluations | Two **vertical initial** data, not the infinite edge sum |
| `carryWeightedVerticalReturn eta h0 h1` | `(ℝ×ℝ) →L[ℝ] CarryVerticalL2`; `eta^k*(a+k*b)` | Yes, `0≤eta<1` | Returns the affine homogeneous vertical part, not a material global boundary sum |
| `realCarryTfvdAnalysis eta` | `CarryVerticalL2 →L[ℝ] (CarryVerticalL2×(ℝ×ℝ))` | Yes | Weighted vertical second difference plus the two initial data |
| `realCarryTfvdSynthesis eta h0 h1` | reverse product → `CarryVerticalL2` | Yes | Causal Green plus return; the existing theorem says S∘T=I |
| `materialTfvdAnalysis` / synthesis | finite material labels → two real quadratures of vertical fibers | Pointwise real-linear lift | Requires a distinct vertical fiber for each material label; no material-edge=depth identification |
| `c2FiberTfvdAnalysis` / synthesis | `GlobalC2BranchCarrier` → core × sign × quadrature × vertical analysis data | Current global API is a LinearMap into a function family | Physical address is decoded first; vertical index is j with depth j+2 |
| `c2OddMaterialTfvdAnalysis` | `OddMaterialState →ₗ[ℝ] C2RealTfvdChannels` | Injectivity proved; no new global norm assertion here | An existing odd-material/address crosswalk, **not** a decoder of consecutive material gradients |
| Green/Parseval source and seed/return channels | PNat material ℓ² → camera Hilbert channels | Existing bounded maps / Parseval isometry | Neither reconstruction nor isometry supplies a sum with coefficients ±1 on infinitely many material edges |

The ordinary product norm in `CarryVerticalL2×(ℝ×ℝ)` is not by itself the
Hilbert direct-sum norm. A standard `WithLp 2` repackaging would be required
for that exact Hilbert claim; no norm identity is inferred from its name.
This is not the main missing seam: its coordinates are still local vertical
trace data.

No local theorem maps the new full seeded-gradient source to these vertical
channels with the desired completed boundary readout. The existing global
C2 incidence equivalence covers **odd physical leg material points**. A
material edge joins two successive positive material integers and includes
even/odd endpoints; it is not the same index. Merely treating its Nat label
as a vertical depth is forbidden and is not done.

## Read-only historical architecture

Repository `thiagomassensini/carry-self-adjoint-operator`, revision
`62b1c0d6b18e70b4c156c3bdf0253893fdb27a35`:

- `CompletedC3AllCutoffHilbertState.lean`: complete ordinary/log gradient
  ℓ² channels, with absolute summability proved first and prefixes converging;
- `CompletedC3BracketTfvdGreenFactorization.lean`: cutoff enriched transport
  **plus separate scalar value/log tails**. Scalar readouts add these tails.
  Its `.greenPort` is only the finite transport projection; a tail-completed
  scalar readout theorem is not a Hilbert realization of that tail;
- `CompletedC3SeededClockBoundaryReduction.lean`: finite seed/gradient blocks
  reconstruct nodal values; shift is closed but boundary calibration is a
  displayed hypothesis;
- `CompletedNativeClockGreenMomentGate.lean` and
  `ProjectiveValveFirstColumnMomentGate.lean`: explicit first-column boundary
  gates, not unconditional realizations;
- `CompletedTfvdGreenAllOrderIntertwining.lean`: finite ports and all-cutoff
  vector convergence, without identifying the omitted scalar tail as a
  bounded boundary operator on raw ℓ².

Thus the historical architecture indeed retained interior **and explicit
completion data**. It does not provide an unconditional current base-two
Hilbert boundary transform to import. No historical dependency, certificate,
calibration or moment premise is added.

## Literal remaining operation

A completed boundary transform must be derived from the source/camera geometry
on its justified domain, **before** assigning a boundary metric. It must
produce the total C2 edge return

```text
lim_(M→∞) ∑ k<M
  (criticalMaterialGradient t (baseTwoCellRightEdge k)
   - criticalMaterialGradient t (baseTwoCellLeftEdge k)).
```

The required readout identity is precisely

```text
beta (T_boundary (baseTwoCompletedUndressedState t))
 = baseTwoCompletedUndressedReadout (baseTwoCompletedUndressedState t)
 = baseTwoCriticalCompleteSignal t.
```

`T_boundary` is a **missing geometric map**, not a Lean object claimed to
exist and not a certificate accepted as hypothesis. The seed stays distinct
from the interior and the total edge return. A possible standard Hilbert
shape is material-edge ℓ² ⊕ seed ℂ ⊕ derived-boundary ℂ, or geometrically
resolved C2 fibers with their boundaries; shape alone does not define the
transform. In particular we do **not** define `T(x)=(x,ell(x))` or put S(t)
into a boundary field. Storing a known scalar limit is insufficient to identify
it with the TFVD trace/return channels.

Without that map there is no new Hilbert lift, clock computation or first
column pairing in this round. The eventual moment gate remains the equality
between the canonical first column and the pairing of a geometrically
completed Hilbert state/jet. It cannot be stated for a state not yet built.

## Verification and publication

All public declarations have central and specific `#assert_analysis_axioms`
and `#print axioms` entries. The allowed footprint is a subset of
`[propext, Classical.choice, Quot.sound]`; no new mathematical axiom or trust
escape. Build/audit exit statuses are recorded after execution below.

Raw no-go increment verification: the module, specific audit, Analysis and
Analysis/Audit all built with `--wfail`, exit 0. Direct kernel elaboration of
the specific audit, all three Analysis/Foundation/Geometry scripts and
`git diff --check` exited 0. No `sorry`, `admit`, `axiom` or `unsafe` occurs
in the new Lean source. The witness norm/readout and both no-go capstones
print exactly `[propext, Classical.choice, Quot.sound]`.
Commit message: `audit: exclude raw L2 completion readout and bounded factorizations`.


## Derived boundary limit: second increment

`BaseTwoCompletedBoundaryLimit.lean` names the **geometrically determined**
return target without packaging it as a Hilbert coordinate:

```text
baseTwoCompletedBoundaryPrefix M t
 = ∑ k<M (G_t(rightEdge k)-G_t(leftEdge k));
baseTwoCompletedBoundaryValue t
 = ∑' k (G_t(rightEdge k)-G_t(leftEdge k)).
```

`baseTwoCompletedBoundaryPrefix_eq_head_sub_seed` identifies each return with
`baseTwoFiniteHead M t - criticalMaterialSample t 1`.
`baseTwoCompletedBoundaryPrefix_tendsto` proves the norm limit to the boundary
value by the already proved summability of **complete cells**, without a free
tail or a new summability premise.

`baseTwoCompletedBoundaryValue_eq_readout_sub_seed` and
`baseTwoCompletedBoundaryValue_add_seed_eq_signal` prove, literally:

```text
boundaryValue t = ell(X(t)) - criticalMaterialSample t 1;
criticalMaterialSample t 1 + boundaryValue t = S(t).
```

Separately, `baseTwoCompletedMaterialInteriorPrefix_tendsto` proves that the
finite material-coordinate interior truncations converge in ℓ² to the same
`baseTwoCompletedMaterialGradientL2 t`. Its coordinate N is a material-edge
cutoff; M in the boundary prefix is a whole-cell cutoff. No identification of
these cutoffs with C2 vertical depth is made.

These are positive completion facts. They are **not** the missing Hilbert
boundary transform: no Hilbert metric on the completion data, no map
`(g,ell(g))`, no additional scalar field equal to S(t), and no extension of
the readout to ℓ² are introduced. The exact scalar boundary target is now a
named, kernel-checked object. The missing operation must geometrically produce
**this** `baseTwoCompletedBoundaryValue`, plus the retained seed, as its
boundary output. A function-family TFVD fiber chart alone does not do so.
The current trace `(x0,eta⁻¹*x1-x0)` is not asserted to equal that return.

The missing identity for a future justified Hilbert boundary transform is:

```text
its_derived_return (baseTwoCompletedUndressedState t)
 = baseTwoCompletedBoundaryValue t,
```

together with retained seed and material provenance. The left-hand operator
is absent locally; it is neither hypothesized in a theorem nor invented from
the right-hand scalar. Thus there is no Hilbert first-column theorem yet.
A realization on the actual source orbit or on the stronger source topology
is not refuted by the raw-ℓ² no-go.

No clock/differentiation computation is attempted: the user required that
only after the geometric Hilbert lift exists. The new limits cannot be used
to claim an autonomous clock or a moment Gram.

First increment published as
`ccb032daa6655a6aec0e0d0454a7256e3950c0ec`.
Second increment commit message:
`feat: identify exact completed boundary and material interior limits`.

Second increment verification: new module, specific audit, Analysis and
Analysis/Audit all build with `--wfail`, exit 0. Direct kernel elaboration,
Analysis/Foundation/Geometry audit scripts and `git diff --check`: exit 0.
Both convergence capstones and the return/readout/signal identities print
`[propext, Classical.choice, Quot.sound]`. Placeholder scan: no matches.
No boundary/Hilbert realization is claimed by these scalar return and ℓ²
interior convergence theorems. The round's status remains the raw no-go,
with the constructive boundary-map gate explicitly isolated.
