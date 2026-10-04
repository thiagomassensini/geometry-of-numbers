# Forensic inventory: the pre-dressing completed material signal lift

Date: 2026-10-04. Starting canonical main:
`d74324f833487ee80cd224d9a43fd37e3edeb84e`.

**Status: PASS_EXISTING_COMPLETED_VECTOR_SIGNAL_LIFT.**
Scope: a complete seeded material-gradient **Banach** vector and its bounded
linear C2 signal readout. This is not a Hilbert moment first column, not a
canonical Gram, and not an identification with the modern depth-amplitude C2
source. The previous missing signal lift is now instantiated locally.

## Source/revision and method

Read-only historical repository `thiagomassensini/carry-self-adjoint-operator`,
revision `62b1c0d6b18e70b4c156c3bdf0253893fdb27a35`. Definitions, types and
premises were read with `git show` / `git grep` at that revision. No old module,
package, certificate, positive sewing assumption or downstream conclusion is
imported. The canonical repository remains the sole destination.

The priority modules were inspected before defining the local lift:

- `CompletedTfvdGreenAllOrderIntertwining.lean`;
- `CompletedNativeCausalGreenProvenance.lean`;
- `CompletedC3ExistingDressedStateAudit.lean`;
- `CompletedNativeClockGreenMomentGate.lean`;
- `C2GeometryNativeSourceBridge.lean`;
- `CompletedNativeTfvdGreenMomentGramBridge.lean`;
- `ProjectiveValveFirstColumnMomentGate.lean`.

Definitions were followed into `CompletedC3AllCutoffHilbertState.lean`,
`CompletedC3BracketTfvdGreenFactorization.lean`,
`CompletedC3GreenFrameOrientedCarrier.lean`,
`CompletedC3ConcreteRealAxisKernelCarrier.lean`,
`CompletedC3SeededClockBoundaryReduction.lean`, and
`C3SeededClockShiftIdentity.lean`. The unrelated conclusions of imported old
modules are not premises of the new proof.

## Candidate inventory (questions 1–10)

| Candidate | Exact carrier / origin | Layer and retained coordinates | Readout and missing chain | Seeded atlas? |
|---|---|---|---|---|
| `canonicalCompletedTfvdGreenPortState z` | `FiniteC3GreenPortCarrier 3`; `completedTfvdGreenLedgerC3Port z (seededCompletedTfvdGreenLedger 1 z)` | Pre-archimedean finite port; two finite Green legs. Equality with `finiteC3GenuineBracketGreenBoundaryPair 3` is a vector equality. | On the native line both legs are the packaged consecutive material slopes. It is not the infinite base-two complete signal or the full seed/value-tail/log-tail ledger. | No |
| `canonicalCompletedTfvdGreenCameraState z` | `CarryGammaComplexCamera`; `c3SixCameraPacking` of that port | Faithful finite six-camera packaging before the scalar Green form; no explicit C/B dressing in this definition | Proven equal to packed bracket port; no natural readout theorem to current S | No |
| `canonicalCompletedTfvdGreenNaimarkState z` | `CarryGammaComplexNaimark`; `c3SixCameraNaimarkRealization` of the port | Finite port promoted to its Naimark realization, not a restored scalar tail | Vector equality to realized bracket port is proved; it does not supply the current complete scalar readout | No |
| `canonicalCompletedTfvdGreenAllCutoffNaimarkState M s` | `RealifiedNaimarkComplexification`; `finiteC3SymplecticNaimarkRealization (3*M)` of the structured completion state's `.greenPort` | Fixed global carrier, finite cutoff vector. Native-line coordinates come from the duplicated slope port. Its norm-limit state exists for `0 < s.re`. | `.greenPort` projects the finite transport; it does **not** read stored value/log tails. Vector convergence is proved, but no current base-two S readout is supplied. | No |
| `canonicalCompletedC3HilbertState s hs` | `CarryVerticalL2 × CarryVerticalL2`, historical complex ℓ² ordinary/log-gradient pair | Complete pre-dressing coordinates; limits of prefixes are proved independently of moments. Crucially the ordinary channel is proved absolutely summable first. | Its ordinary source formula matches the local material gradient. For current S one needs the seed and base-two edge boundary readout. The local reconstruction below proves that readout in the ordinary channel's ℓ¹ presentation. | No |
| “existing dressed state” in `canonicalCompletedC3ExistingDressedState_eq_orientedImage` | Actual object is `canonicalCompletedC3RealAxisPositiveState`; `WithLp 2` of ordinary/log Parseval channels and complexified real residual | Post-Green/Parseval source packaging, **not** explicit multiplication by C/B in this definition. Its source is the completed ordinary/log pair plus `infiniteReflectedGreenEnergy • completedTfvdResidualGenerator`. | The vector image of the oriented source is proved. Matching its positive kernel to the completed ledger is the explicit unproved `CanonicalCompletedC3ConcreteRealAxisPositiveSewing`. | No |
| `canonicalCompletedC3ConcreteRealAxisGreenState z` (next wrapper) | Same positive carrier, multiplied by `sqrt 2 * completedNativeOperatorCharacteristic z` | This wrapper is after scalar characteristic dressing. It must be distinguished from the preceding positive state. | Normalization away from a nonzero scalar recovers the positive state. That statement does not prove the positive sewing premise. | No |
| `seededClockAtlasJet block r` | `WithLp 2 (ι → EuclideanSpace ℂ (Fin 4))`, `Fintype ι`; reconstructed four-node clock powers | Finite full seed/gradient blocks; independent of moment definitions, but not an infinite completion | Its Gram is `seededClockAtlasCoefficient`; equality to a completed boundary Taylor column explicitly consumes `hboundary` / `HasCorrectedNativeSeededClockBoundaryTransport`. | This is the atlas itself, not one of the other states |

The structured `canonicalC3BracketTfvdCompletionState M s` deserves a separate
warning. It retains finite enriched transport and **scalar** value/log tails.
Its scalar value projection is proved cutoff-completed, whereas its Green port
projects only finite transport. Equality of the two projections' states is not
proved and must not be inferred. It concerns the historical camera 3 chart,
not literally the present camera 2 cell family.

Historical provenance theorems reconstruct causal-response + return into the
completed gradient channel. These are unconditional lossless source identities.
Their Wronskian/positive-kernel sewing and the Taylor/forward-difference moment
comparison have separate displayed premises. None is needed here.

### What feeds `seededClockAtlasJet`?

Each `SeededClockBlock` stores four real frequencies and
`state : SeededC3Data = ℂ × (Fin 3 → ℂ)`. The native specialization is

```text
nativeBlockSeededData m s =
  (positiveDirichletValue s (3*m), nativeC3BlockGradient m s).
```

`seededRecover` reconstructs the four material values at `3m+1,…,3m+4`.
`seededClockMaterialRawJet` iterates the clock on this full seed/gradient data
and then reconstructs. The general atlas accepts supplied blocks; it is not
fed by a proved archimedean-completed vector. Its first-column calibration
remains explicit. It is related by source architecture to the completed
gradient channel, not the same vector or same carrier.

## Candidate selected: completed ordinary material gradient + incoming seed

The closest pre-dressing candidate is the **ordinary channel of
`canonicalCompletedC3HilbertState`**, before its Green/Parseval promotion.
Historical `CompletedC3AllCutoffHilbertState.lean` proves
`summable_norm_positiveDirichletGradient` and ℓ¹ membership before weakening
it to ℓ² membership. Its index denotes consecutive material edges, not an
intrinsic C2 positional depth. That provenance is explicit in the local names.

The reconstruction uses the existing local `criticalMaterialSample` only:

```text
f_t(n) = n^(-1/2) exp(-it log n), n>0
G_t(j) = f_t(j+2) - f_t(j+1)
E = ℂ × ℓ¹(ℕ,ℂ)
X(t) = (f_t(1), G_t).
```

`criticalMaterialGradient_eq_nativeLinePowerDifference` proves the native-line
coordinate formula with the existing `baseTwoDressingParameter = 1/2+it`.
This matches the historical ordinary channel's source formula, not its carrier
norm. No theorem is asserted across unimported packages.

The local first-difference estimate, derived by the mean-value bound and the
already proved sample/cpow identity, is

```text
‖G_t(j)‖ ≤ ‖criticalMaterialExponent t‖ (j+1)^(-3/2).
```

Thus every real t gives an absolutely summable full material-gradient state.
No summability or nonzero-condition hypothesis is received. This is a standard
Mathlib lp carrier chosen from that preexisting absolute-summability property,
not a Hilbert space fitted to moments. The product norm is used only for
continuity; it is not declared a quadratic energy.

`baseTwoCompletedMaterialGradientL2` also stores these same coordinates in
standard ℓ²; `baseTwoCompletedMaterialGradientL2_apply` proves coordinate
agreement with the ℓ¹ state. It does not identify the two norms or extend the
summation functional continuously to ℓ².

## Complete vector before readout, with recoverability

`baseTwoCompletedUndressedState_recover` proves for every material n:

```text
X(t).seed + ∑ j<n, X(t).gradient(j) = f_t(n+1).
```

Consequently the seed/gradient change of coordinates loses no material sample
or real/imaginary quadrature. The state has all coordinates, not a finite head
or a scalar tail inserted into a chosen vector coordinate. Standard lp
summation of coordinate singles supplies the completed vector presentation;
no scalar signal is used to define it.

The current camera indices, not historical camera constants, determine the
edges. With the existing center `c_k=4(k+1)`:

```text
leftEdge(k)  = baseTwoLeftLeg k - 1 = 4k+2
rightEdge(k) = baseTwoCenter k - 1  = 4k+3
B_k(t) = G_t(rightEdge(k)) - G_t(leftEdge(k)).
```

`baseTwoCriticalCenterCell_eq_gradientEdges` is the exact source-level identity.
The scalar readout is applied to the full seeded vector only after construction:

```text
ell(z,g) = z + ∑' k, (g(rightEdge(k)) - g(leftEdge(k))).
```

It is a **continuous complex-linear map on E**: injective edge restrictions
are bounded on ℓ¹, their difference is bounded, and Mathlib `lp.tsumCLM`
performs the final sum. No new unbounded boundary functional is hidden.

## Closed signal gate and dressing consequence

Main capstone:

```lean
baseTwoCompletedUndressedReadout_eq_signal (t : ℝ) :
  baseTwoCompletedUndressedReadout (baseTwoCompletedUndressedState t)
    = baseTwoCriticalCompleteSignal t
```

It follows from the existing complete-cell signal definition and the exact
edge identity. The head/tail completion theorem is not reproved. Neither
moments, positivity nor a fitted vector enter this equality.

The previous generic dressing gate now has a concrete instantiated input:

```text
ell(baseTwoVectorDressing t (X t)) = baseTwoCanonicalResponse t.
```

This is `baseTwoCompletedUndressedReadout_dressed_eq_response`. It uses the
already proved nonzero scalar dressing equivalence, after the new undressed
readout equality. It does not create a spectral moment representation.

## What remains open, precisely

**No missing signal-readout equality remains for this Banach lift.**
A whole-cell vector lift was not needed: the historical ordinary-gradient
architecture, completed in its standard absolutely summable presentation and
with the seed retained, already supplies the correct vector/readout chain.

This does not yet provide a Hilbert vector `v_completed` whose self-adjoint
clock powers give canonical log-derivative moments. In particular, the new
ℓ¹ readout is not asserted to be a continuous functional on the old ℓ² carrier,
nor to identify the modern depth-amplitude C2 source with the material-amplitude
observable. Hilbert/Green realization of this same completed observable and
its first-column metric remain a separate task; there is no typed theorem
`h_r = Re ⟨X(0),L^(2r)X(0)⟩` on this Banach carrier.

The prior generator product-rule correction `D'(t) X(t)` is unchanged.
No autonomous generator, all-order vector regularity, moment recurrence,
Hankel/PosDef, or height operator is constructed in this round.

## Provenance and negative guards

- Every new vector coordinate comes from existing material samples before
  any mention of the canonical moments.
- All material integers and camera edges are locally derived, with no choice
  or fitted coefficients.
- Full seed/gradient reconstruction precedes scalar readout.
- Readout coincidence does not imply equality to Naimark, oriented or atlas
  states; no such state equality is claimed.
- Material amplitude `n^(-1/2)` is never equated with depth amplitude
  `2^(-k/2)`; material edge j is never identified with vertical depth.
- No bare incidence, causal zero-seed candidate or refuted complex-Taylor
  product ledger is used as the completed moment carrier.
- Historical sewing/representation hypotheses and unrelated downstream
  imports are neither copied nor assumed.

## Kernel/build/audit publication ledger

New local files: `BaseTwoCompletedGradientSignalLift.lean` and its specific audit.
All public definitions/theorems have central Analysis guards and `#print axioms`.
Allowed Analysis footprint: `[propext, Classical.choice, Quot.sound]` only.

Commands: `lake build --wfail` new module, specific audit, Analysis and
Analysis/Audit; direct elaboration of the specific audit; scripts
Analysis/Foundation/Geometry; placeholder scan and `git diff --check`.
Verification completed: all four `--wfail` targets, direct kernel elaboration,
Analysis/Foundation/Geometry audit scripts and `git diff --check` exited 0.
The two new Lean files have no `sorry`, `admit`, `axiom` or `unsafe` declaration.
The summability, complete-state recoverability, cell-edge identity, signal
readout and dressed-response capstones each print exactly
`[propext, Classical.choice, Quot.sound]`. All public declarations pass the
Analysis footprint guard; some coordinate definitions have a smaller footprint.
Commit message: `feat: recover complete seeded material gradient signal lift`.
