# Real TFVD / center–leg moment seam

## Question and order of construction

Can proven C2 material incidence, real vertical TFVD reconstruction and a
completed center–leg readout realize `baseTwoCanonicalMomentSequence` as one
real parity Gram family? No moment is allowed to choose a vector or its
coefficients. A scalar response embedded into one dimension would not answer
this question.

The previous material-orbit/Parseval candidate is diagnostic. Parseval
preserves its inner products and its first-column residual; it does not
identify that candidate with a completed boundary readout.

## Integrated increment A: neutral real coefficient algebra

`PolarizedMomentCoefficients.lean` defines `parityJetNumber`,
`realMomentDiagonalCoefficient` and `polarizedRealMomentCoefficient` in `ℝ`.
The four parity cases are proved, as is the exact crosswalk
`polarizedRealMomentCoefficient_eq_parityMomentKernel` to the existing Gram
API. `polarizedRealMomentCoefficient_shift` moves one order between arguments.
`parityJetNumber_injective` distinguishes parity labels. Taylor order is not
a material address or a vertical depth.

These coefficients do not construct a carrier and assert no concrete Gram.
They are valid for every real sequence, without positivity premises.

## Historical comparison (read-only)

Repository `thiagomassensini/carry-self-adjoint-operator`, revision
`62b1c0d6b18e70b4c156c3bdf0253893fdb27a35`:

- `CompletedGreenJetCoefficientRecurrence.lean`: algebraic polarization.
- `BR2CenterLegMomentKernel.lean`, `BR2IncidenceStrictPositivity.lean`,
  `BR2BracketTfvdIncidenceTransport.lean`,
  `BR2ProjectiveHilbertIncidenceTransport.lean`: incidence transport blueprint.
- `CompletedNativeHPGateAudit.lean`, `ProjectiveTfvdCarrier` section: the
  historical transport still consumed a center–leg readout premise.
- `NativeCausalCenterLegNoGoAudit.lean`,
  `CompletedNativeTaylorResidualNoGo.lean`,
  `BR2RadialNormalizedComplexJetNoGo.lean`: negative representation guards.
- `docs/CHECKPOINT_AUTO_ADJUNTO.md`: positive ordinary Hilbert readout and
  skew/Wronskian readout were not proved to coincide.

Only neutral real algebra is reconstructed in increment A. No historical
package, spectral result or complex Taylor carrier is imported.

## Provenance test for increment A

No vector is defined. No incidence or amplitude is reinterpreted. No readout
or moment is used to select vector coefficients. The coefficient-side kernel
is not a Gram proof. Real TFVD incidence and the completed center–leg equality
remain separate targets.

## Kernel and operational checks

Every public definition and theorem is guarded in the main Analysis audit and
printed in `PolarizedMomentCoefficientsAudit.lean`. The permitted footprint is
`propext`, `Classical.choice`, `Quot.sound`; no new mathematical axiom.
The publication record and subsequent incidence gate are appended below.

Increment A validation: `lake build --wfail` for the new module, its audit,
Analysis and Analysis.Audit: exit 0. All three repository audit scripts: exit
0. `git diff --check`: exit 0. Kernel prints report the standard Analysis
footprint for coefficient theorems and `[propext, Quot.sound]` for the parity
index injection. No placeholder or trust escape appears in the new modules.
Publication commit subject: `feat: prove real polarized parity coefficient algebra`.

## Increment B/C/D: actual real vertical fibers and address independence

`C2RealFiberTfvdIncidence.lean` retains the existing Hilbert carrier
`GlobalC2BranchCarrier = ℓ²(PositiveOddCore × C2BranchAddress, RealPlaneHilbert)`.
Each fixed core, direction and real quadrature is extracted into the existing
`RealCarry.CarryVerticalL2`. The extraction's ℓ² membership follows by an
injective restriction of the square sum and coordinate norm domination.
No new Hilbert norm is invented.

The vertical chart is exactly `j ↦ depth = j + 2`, inherited from
`C2BranchAddress`. A shift of j advances physical depth, not material n.
`C2RealVerticalChannels` and `C2RealTfvdChannels` are labelled function spaces
of existing vertical carriers. No global Hilbert norm on these function
spaces is asserted. The global inner product remains on the existing branch
Hilbert carrier.

`c2FiberTfvdAnalysis` applies R2 independently to all those fibers.
`c2FiberTfvdSynthesis_analysis` reuses the existing left inverse and retains
trace/return in each quadrature. `c2FiberTfvdAnalysis_injective` follows from
this reconstruction. `c2OddMaterialTfvdAnalysis_injective` first decodes the
provenance-correct material incidence, then applies this faithful analysis.
`c2OddMaterial_verticalCoordinate` proves the exact material/fiber crosswalk.
The critical specialization uses the already derived vertical ratio.

For an explicit incidence family, the canonical unit odd core has both
physical signs at every depth `j+2`. `c2ParityIncidenceAddress` assigns even
labels to left legs and odd labels to right legs of the same fixed-core
fibers. `c2ParityIncidence_left`, `_right`, `_depth_recovery`, and
`_center_ne_leg` certify the actual physical incidence. All centers are even;
all legs are odd, so even cross-index center–leg pairs are distinct.

`c2RealIncidenceJet` is the coordinate basis in the **existing** global branch
carrier, with real quadrature seed `(1,0)`. Its coefficients do not involve
moments, response, dressing or a fit. Unique address pivots prove combined
independence. Injective TFVD analysis transports that independence in
`c2RealTfvdIncidenceJet_linearIndependent`, with even/odd and every finite
prefix corollaries. These are incidence jets, **not** derivatives of the
completed dressed observable and **not** designated canonical moment jets.

### Provenance test

1. Vectors exist before mentioning the canonical moments: YES.
2. Incidence comes from existing C2 integers/core/sign/depth: YES.
3. Exact synthesis is available before any proposed inner-product readout: YES.
4. Carrier defined retroactively from a readout: NO.
5. Moments select vector coefficients: NO.
6. Material and depth amplitudes identified: NO. No amplitude is inserted in
   this coordinate incidence basis; the existing physical source is only
   decoded by its previously proved incidence equivalence.

### Remaining gate

The current APIs give faithful reconstruction and independent incidence
channels. They do not identify their reconstructed inner product with the
completed, dressed logarithmic-moment coefficient. A center–leg boundary
readout of the completed synthesis still needs a concrete state/channel
crosswalk. Analyticity of the scalar response does not define such a vector
readout. Neither Gamma sewing nor an assumed vector completion is added.
No Hankel positivity is inferred from incidence independence alone.

Increment A was published as
`9d112a3423958692ace07dfb4d3ad5c00f057a10`, with main/origin/GitHub equal.

Increment B/C/D validation: isolated `--wfail` module build, specific audit,
Analysis and Analysis.Audit: exit 0. Analysis, Foundation and Geometry scripts:
exit 0. `git diff --check`: exit 0. Public transport, reconstruction,
injectivity, incidence and independence statements are guarded and kernel
printed; their footprint is at most the three standard Analysis axioms.
Publication commit subject:
`feat: transport provenance-preserving C2 fibers through real TFVD`.

## Final readout gate and a representation-specific exclusion

Status: **PASS_REAL_TFVD_INCIDENCE_TRANSPORT_CENTER_LEG_OPEN**.
This status certifies faithful real fiber transport and incidence independence,
not existence of completed canonical moment jets.

`RealTfvdCenterLegMomentSeam.lean` types the missing bilinear equation in ℝ:

```text
polarizedRealMomentCoefficient h (parityJetNumber i) (parityJetNumber j)
  = inner ℝ (jet i) (jet j)
```

for the certified C2 center–leg incidences.
`HasBaseTwoCanonicalTfvdCenterLegReadout` specializes this target to the
already concrete canonical sequence. It is a proposition about an independently
constructed family, not a field supplying the conclusion and not a proved
certificate. `c2RealTfvdCenterLegReadout_iff_parityGram` explains exactly why
this equality would identify all four parity blocks. It does not prove it.
`baseTwoRealTfvdCenterLegResidual` records the exact real coefficient-minus-inner
residual, and `_zero_iff` types the remaining equality.

The simplest independently constructed vectors, `c2RealIncidenceJet`, are
ordinary coordinate incidence vectors. Their actual inner product is
`if i = j then 1 else 0`, proved by `c2RealIncidenceJet_inner`. They therefore
cannot themselves be completed Hankel jets: the even entries `(0,2)` and
`(1,1)` both request h₂ but their inner products are 0 and 1.
`c2RealIncidenceJet_not_parityMomentGram` proves this for **any** real sequence;
`c2RealIncidenceJet_not_canonicalCenterLegReadout` and
`c2RealIncidenceJet_residual_not_all_zero` give the canonical specialization.
No comparison of numerical moments or adjustment of constants is involved.

This is a no-go **only for the bare coordinate incidence representation**.
It does not refute a completed channel/boundary readout, the canonical moments,
or the theory. TFVD reconstruction retains that basis; it does not convert its
ordinary diagonal inner product into the completed kernel. We do not try to
prove this candidate's residual zero, just as the previous Parseval orbit
candidate was not designated the correct completed readout.

### Smallest remaining seam

A concrete completed **real** state/channel readout, constructed from the
synthesized geometry before comparison with moments, must be identified
bilinearly with the polarized coefficients of the canonical dressed response.
Neither scalar all-order regularity nor `H Φ = -Φ'` supplies that vector
identity. The current proof does not establish that a separate vector Gamma
realization is required; it establishes that bare incidence reconstruction is
insufficient. No `xiState`, Gamma sewing premise, free tail, moment-fitted
vector or hidden center–leg assumption is introduced.

Consequently full canonical parity Gram, Hankel PSD and PD remain OPEN.
The proved all-order independence concerns incidence families only; it is not
independence of a presently identified canonical moment-jet family. No
unbounded clock is applied, so no all-order domain assertion is used or
claimed. The existing general C2 logarithmic-domain gate remains unchanged.

### Provenance test for the gate module

1. The tested incidence vectors predate canonical moments: YES.
2. Their centers/legs are already certified physical C2 incidences: YES.
3. Exact fiber synthesis/recovery is proved upstream: YES.
4. A readout defines the carrier retroactively: NO.
5. A moment chooses a vector coefficient: NO.
6. Depth amplitude equals material amplitude: NO.

Only existing scalar canonical moments are used on the coefficient side of
an audit residual. No scalar is embedded as a Hilbert vector to prove Gram.

Increment B/C/D was published as
`9740b3e65010a9743b20c18da91dca8d9f98d5b1`, with main/origin/GitHub equal.

Final gate-module validation: `lake build --wfail` for
`RealTfvdCenterLegMomentSeam`, its specific audit, Analysis and Analysis.Audit:
exit 0. `bash scripts/audit-analysis.sh`, `audit-foundation.sh`,
`audit-geometry.sh`: exit 0. `git diff --check`: exit 0. Every public gate,
residual and representation-exclusion theorem has `#assert_analysis_axioms`
and `#print axioms`; the printed capstone footprint is
`[propext, Classical.choice, Quot.sound]`. All newly added Lean sources pass
the placeholder/trust-escape scan. R2, Foundation and Geometry source files
are unchanged. There were no preexisting dirty files in the canonical checkout.
Final publication commit subject:
`audit: isolate completed real center-leg readout from incidence basis`.
No further mathematical stage is implemented in this round.
