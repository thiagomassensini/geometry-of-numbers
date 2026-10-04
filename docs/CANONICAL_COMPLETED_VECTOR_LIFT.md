# Completed vector response: inventory and exact dressing gate

Date: 2026-10-04. Starting main:
`73f5e192a16eaf4ad43f8516c55b921753aa4f53`.

**Status: PASS_COMPLETED_VECTOR_LIFT_GATE_ISOLATED.**
This is a diagnostic status. No completed vector response or canonical moment
Gram has been constructed. The new kernel-checked result separates scalar
vector dressing from the still missing complete vector synthesis/readout.

## Inventory before definitions

| Object | Existing type and role | Where scalar readout enters |
|---|---|---|
| `finiteMaterialOrbit N t (historicalInitialState N)` | Existing finite material Hilbert vector; material coordinate `j+1` | `finiteHeadReadout (historicalCameraWeights 2 M)` |
| `baseTwoFiniteHead M` | Complex scalar function | Exactly that finite vector readout, by `baseTwoFiniteHead_eq_historicalFiniteHeadReadout` |
| `baseTwoCriticalCompleteTail M` | Scalar sum of complete omitted bracket cells | Defined using the already scalar `baseTwoCriticalCenterCell` |
| `baseTwoCriticalCompleteSignal` | Complex scalar seed plus the sum of whole cells | It is scalar from its definition; no complete Hilbert-vector lift is supplied there |
| `baseTwoSynthesizedSignal M` | Scalar head + exact scalar tail | Function equality with the complete scalar signal precedes every normalized jet |
| `c2GlobalGreenInputIsometry t V` | Full provenance-correct material `State` vector | It is a different vector source, not a proved lift of this material-amplitude bracket signal |
| `greenParsevalAnalysis (c2GlobalGreenInputIsometry t V)` | Existing complete Green analysis vector | Diagnostic orbit pairings do not identify a completed boundary observable |
| `MaterialVerticalCarrier N` / TFVD channels | Material fibers of two real vertical channels, with exact boundary reconstruction | No local theorem makes their readout equal to the complete scalar signal |
| `B`, `B⁻¹` | Concrete scalar camera function / inverse, and normalized Taylor germ | No preexisting channel or boundary operator realizing the quotient was found |
| `C` | Concrete scalar polynomial/exponential/Gamma dressing and germ | No preexisting vector realization of its boundary metric was found |

There is no single local vector-to-scalar chain already certifying all of
`S`, `B⁻¹`, `C`. On the finite head chain the last vector is the finite material
orbit, and `finiteHeadReadout` is the exact scalarization point. On the C2/Green
chain full vectors do exist, but the corresponding complete signal readout is
not identified. These two chains must not be conflated.

This inventory is a source inspection, **not a Lean theorem that no future
vector lift can exist**. Scalar all-order regularity does not establish Hilbert
all-order regularity or identify the material and depth amplitudes.

## Historical blueprint, read only

Repository `thiagomassensini/carry-self-adjoint-operator`, revision
`62b1c0d6b18e70b4c156c3bdf0253893fdb27a35`:

- `CompletedNativeClockGreenMomentGate.lean`: `seededClockAtlasJet` lives in
  `WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))`. It retains four reconstructed
  nodal coordinates per finite block. Its coefficient is an actual inner
  product. Its equality with the completed boundary column is an explicit
  **hypothesis** `hboundary`, not an instantiated completed vector.
- `ProjectiveValveFirstColumnMomentGate.lean`: lossless TFVD reconstruction
  does not imply the metric shift or boundary calibration. The first-column
  reduction is conditional on a transport law for a previously defined family.
- `C2GeometryNativeSourceBridge.lean`: scalar exact head/tail identities and
  corrected scalar coefficients coexist with a named nonvanishing-status
  boundary residual. The seeded-clock-to-camera coefficient theorem takes
  `HasCorrectedNativeSeededClockBoundaryTransport` as an input. The finite
  atlas is a finite atomic power sum; that expansion does not eliminate the
  boundary hypothesis.
- `CompletedNativeTfvdGreenMomentGramBridge.lean`: the vector TFVD port
  equality is separate from the product-ledger metric. A completion vector
  `xiState`, factor Green representation, and Taylor/forward-difference
  residual identities are inputs to conditional theorems. They are not a
  proved realization available for local import.

The structural local analogue of the finite seeded clock is the finite material
clock/Krylov family. It is not a literal four-node seeded atlas port. The full
local C2 source retains provenance and has Parseval transport, but no theorem
identifies it with the historical completed boundary calibration. None of these
historical imports, gates, certificates, or downstream conclusions is copied.

## New neutral vector operation

`BaseTwoCompletedVectorLiftGate.lean` defines only

```text
D(t) = canonicalArchimedeanCompletion t * (baseTwoCanonicalCameraFactor t)⁻¹
baseTwoVectorDressing t = D(t) • id
```

The operation is complex-linear on a **preexisting** normed complex carrier.
`baseTwoGreenVectorDressing` specializes it to the existing Green `State`.
No carrier, seed, readout, or completed vector is selected using moments.
Complex multiplication keeps both real quadratures; it is not an asserted
real scalar action on `CarryVerticalL2`. No completion metric realization is
inferred from this ordinary scalar action.

`canonicalArchimedeanCompletion_ne_zero` proves nonvanishing on every real
parameter: the polynomial factors have real parts ±1/2, the exponential is
nonzero, and the Gamma argument has real part 1/4. This uses standard Gamma
nonvanishing directly, without a zeta identification. `D` is consequently
nonzero and analytic there. The vector action is injective, with inverse
scalar action `D(t)⁻¹`; its exact norm is `|D(t)| ‖x‖`. It is **not claimed
isometric**.

For any independently constructed `X` and complex-linear `ell`, the kernel
proves the precise residual:

```text
ell(D(t) • X(t)) - R(t) = D(t) * (ell(X(t)) - S(t)).
```

Thus `baseTwoVectorDressing_function_readout_iff` says that the full dressed
readout equality holds iff the undressed complete synthesis equality holds:

```text
∀ t, ell(X(t)) = baseTwoCriticalCompleteSignal t.
```

This is the smallest **readout-lift gate**, after discharging dressing
nonvanishing. It is an equivalence, not a certificate instantiated by assuming
the desired equality. A local geometrically constructed `X` and its boundary
readout `ell` realizing this equation remain unidentified. It would be false
to say that two already identified completed vector objects only need rewriting.

`baseTwoDressedFiniteOrbit_add_tail` tests the actual finite vector chain:

```text
finiteHeadReadout(D(t) • finiteMaterialOrbit(t, historicalInitialState))
+ D(t) * baseTwoCriticalCompleteTail M t = R(t).
```

The missing whole-cell tail remains explicit. This theorem neither embeds a
scalar tail into a fitted coordinate nor promotes the head into a full vector.
`baseTwoVectorDressing_parseval` proves that the scalar action commutes with
the actual complex-linear Parseval map; this cannot supply a missing readout.

## Generator audit

For a prior differentiable vector path `X`:

```text
(D X)' = D X' + D' X.
```

If a total linear clock `L` already gives `X' = -i L X`, then
`baseTwoVectorDressing_clock_derivative_residual` proves

```text
(D X)' - (-i L(D X)) = D' X.
```

`baseTwoVectorDressing_same_clock_iff` characterizes keeping that same clock:
the extra vector `D'(t) • X(t)` must vanish. No vanishing is assumed, and no
claim that it is nonzero at every time is made. A time-dependent scalar
connection is not automatically a new autonomous self-adjoint generator.
These statements use total linear maps only. They do not apply unbounded
material log powers outside their domains or cure the C2 logarithmic-moment
regularity gate.

## First column: still a separate open question

Even a future proof of `ell(X(t)) = S(t)` would certify a linear response
readout, not its quadratic moment metric. No vector has been certified as
`v_completed`, and no spectral sequence is proved to satisfy the canonical
log-derivative recurrence. The exact later parity gate remains

```text
baseTwoCanonicalMomentSequence r = Re ⟨v_completed, L^(2*r) v_completed⟩,
```

with independently justified operator, normalization and all-order domains.
Scalar dressing can change the generator as above; this formula is a target,
not a conclusion about the present scalar-dressed source. Uniqueness may only
be used after independent verification of the same coefficient recurrence.

## Provenance answers

1. No new vector is chosen; the carrier operation accepts any preexisting
   vector and the finite test uses the already existing material orbit.
2. All cell indices and the exact omitted tail come from the local camera
   synthesis theorem.
3. No scalar response or moment is embedded to manufacture a vector synthesis.
4. No moment chooses coefficients, norm or seed.
5. No equality `2^(-k/2) = n^(-1/2)` is used.
6. No bare incidence, causal zero seed or refuted complex-Taylor product ledger
   is revived. Their representation no-gos remain unchanged.
7. No Hankel/PosDef/Jacobi/height theorem is asserted.

## Verification and publication

Public declarations are guarded and printed in `Analysis/Audit.lean` and
`BaseTwoCompletedVectorLiftGateAudit.lean`. Allowed transitive axioms are only
`propext`, `Classical.choice`, `Quot.sound`.

Commands: `lake build --wfail` for the new module, specific audit, Analysis and
Analysis/Audit; direct elaboration of the specific audit; Analysis/Foundation/
Geometry audit scripts; forbidden-placeholder scan and `git diff --check`.
All listed commands completed with exit status **0**. All eighteen public
declarations passed the kernel guards and printed exactly the permitted
`[propext, Classical.choice, Quot.sound]`. Foundation remains axiom-free;
Geometry remains within its own existing footprint.
Commit message: `audit: isolate completed vector synthesis and scalar dressing gate`.
