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
