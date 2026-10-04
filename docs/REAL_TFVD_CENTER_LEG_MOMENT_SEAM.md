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
