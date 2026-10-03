# Canonical downstream dressing and the moment seam

Initial main: `24a01bfad74ac85fff51bc5b6f6191cf1e19f8e1`.
Branch: `base-two-canonical-dressing`.

## Question and causal order

Arbitrary camera/completion germs do not justify unconditional Gram positivity.
We first fix concrete germs downstream of the already-synthesized base-two
material signal. Synthesis precedes dressing, normalized jets and moments.
The dressing does not select the critical exponent, amplitude or head/tail.
The modern depth-amplitude source and historical material-amplitude observable
remain distinct until a separate crosswalk is proved.

## Increment A: exact camera denominator

`BaseTwoCanonicalCameraDressing.lean` defines

$$s(w)=\tfrac12+iw,\qquad B(t)=(1+2^{-s(t)})(1-2^{1-s(t)}).$$

The negative material phase is consistent with $n^{-s(t)}$. At the center,
$B(0)=-2^{-1/2}$. For every real time, $|2^{-s(t)}|<1$ and
$|2^{1-s(t)}|>1$, so neither factor vanishes. This argument uses no zeta.

`baseTwoCanonicalCameraFactor_formula`,
`baseTwoCanonicalCameraFactor_zero`,
`baseTwoCanonicalCameraFactor_ne_zero`,
`baseTwoCanonicalCameraFactor_analyticAt`, and
`baseTwoCanonicalCameraFactor_contDiff` are the exact local results.
The series coefficients are explicitly
$r!^{-1}\,\mathrm{iteratedDeriv}_r B(0)$, proved by
`baseTwoCanonicalCameraFactorSeries_coeff`. Its constant is $B(0)$ and is
nonzero (`baseTwoCanonicalCameraFactorSeries_constantCoeff_ne_zero`).

This increment does not yet replace the completion germ or prove the dressed
all-order response identity, phi(0) nonvanishing or concrete-moment uniqueness.
No Gram, positivity, Jacobi or height result is inferred.

## Read-only provenance

Historical comparison: `carry-self-adjoint-operator` at
`62b1c0d6b18e70b4c156c3bdf0253893fdb27a35`, files
`CompletedOperatorCharacteristic.lean`, `CompletedNativeCharacteristic.lean`,
`CompletedNativeAllOrderCameraBridge.lean`, `CompletedNativeRealWeylMoments.lean`,
and `C2GeometryNativeSourceBridge.lean`.
The camera definition originates in its pinned `native-carry-spectral-weyl`
package, `NativeCarrySpectralWeyl/Camera/Factors.lean`, revision
`298d83c9351e308a5213b9f5ac32e44087f98a9f`.
No package or theorem from those sources is imported. No scalar/zeta
identification was used as a proof premise.

## Audit and next gates

Every public declaration is checked by the dedicated camera audit and the
central Analysis audit. Footprint is within `propext`, `Classical.choice`,
`Quot.sound`. Build/audit commands and publication commits are recorded as
increments complete. The future Gram theorem must identify actual global
orthogonal jets with this definitive scalar moment sequence; it cannot receive
positivity or Gram representation as a substitute for that proof.

### Increment A verification

All exit status 0: `lake build --wfail` for camera module, camera audit,
`GeometryOfNumbers.Analysis` and `GeometryOfNumbers.Analysis.Audit`;
`bash scripts/audit-analysis.sh`, `audit-foundation.sh`, `audit-geometry.sh`;
`git diff --check`. Dedicated and central audits execute both dependency
allow-list guards and `#print axioms` for every public declaration. No proof
placeholder or trust escape occurs in the new source. The mathematical
publication commit is the commit introducing this increment; its exact SHA
will be recorded in the following increment (a commit cannot contain its own SHA).
