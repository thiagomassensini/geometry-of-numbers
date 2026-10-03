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

## Increment B: explicit archimedean completion

Increment A was published in `3c0010f87afec21356df7af563ac8a5de72d856c`.

`BaseTwoCanonicalArchimedeanDressing.lean` defines directly

$$C(t)=\tfrac12s(t)(s(t)-1)\exp\bigl(-\tfrac{s(t)}2\log\pi\bigr)
\Gamma\bigl(\tfrac{s(t)}2\bigr).$$

This is the historical `nativeXiCompletionFactor` formula with a neutral
name; no identification with xi or zeta is asserted or needed.
In each complex quarter-ball around a real time, the Gamma argument has
positive real part. Its differentiability there and Cauchy regularity give
`canonicalArchimedeanCompletion_analyticAt` and `_contDiff`.

`canonicalArchimedeanCompletion_zero` proves

$$C(0)=-\tfrac18 e^{-\log\pi/4}\Gamma(1/4).$$

`canonicalArchimedeanCompletion_zero_re_neg` uses the classical positive
Gamma integral at $1/4$, and `_zero_ne_zero` follows. No zero information
from another function enters the proof. The completion series is the
factorial-normalized Taylor coefficient sequence, with exact coefficient
and nonzero-constant theorems.

At this increment the two concrete dressing germs are fixed, but the
all-order response-series crosswalk and concrete phi(0) proof are separate
next obligations. No Gram or positivity theorem is claimed.

### Increment B verification

Exit status 0 for the archimedean module and dedicated audit builds,
Analysis and central Audit builds (`--wfail`), all three audit scripts,
and `git diff --check`. All new public declarations have kernel dependency
guards and printed axioms within the standard three-axiom footprint.

## Increment C: concrete response and unique moments

Increment B was published in `6d8010685ddcb191f267820b0aacfecbe7078f62`.

### Function before coefficients

Let $S(t)=\texttt{baseTwoCriticalCompleteSignal}(t)$, already synthesized
from complete cells with its derived whole-cell tail. Define

$$R(t)=C(t)\,S(t)\,B(t)^{-1}.$$

`baseTwoCanonicalResponse_analyticAt` proves local analyticity for every
real time. `baseTwoCanonicalResponseSeries` specializes the existing response
ledger to the two concrete germs. The exact all-order identification is
`baseTwoCanonicalResponseSeries_eq_normalizedJets`, equivalently
`baseTwoCanonicalResponseSeries_coeff`:

$$[t^r]\mathcal R = (r!)^{-1}\,\mathrm{iteratedDeriv}_r R(0).$$

The proof uses the iterated Leibniz identity, the exact binomial/factorial
identity and the inverse-germ product identity. No derivative/tsum interchange
and no scalar/zeta identification is used. `baseTwoCanonicalClosedResponse_eq`
identifies every cutoff ledger with this same series; no arbitrary tail remains.

### Center nonvanishing, proved rather than received

At time zero, the material samples are real $n^{-1/2}$. This function is
convex on $(0,\infty)$: its second derivative is nonnegative. Midpoint convexity
therefore proves each complete cell has nonnegative real part
(`baseTwoCriticalCenterCell_zero_re_nonneg`). The separately retained seed
then gives $S(0)>0$, with imaginary part zero, using the already-proved
summability of complete cells. Since $C(0)<0$ and $B(0)<0$,

$$\phi_0=\operatorname{Re}R(0)>0.$$

This is `baseTwoCanonicalPhi_zero_pos`, hence `_zero_ne_zero`. No numerical
value or zero-location claim is used.

### Definitive real-even convention and recurrence

The existing convention is preserved exactly:

$$\phi_r=\operatorname{Re}[t^{2r}]\mathcal R,
\qquad \Phi(u)=\sum_{r\ge0}\phi_ru^r.$$

`baseTwoCanonicalPhi_eq_normalizedEvenJet` includes the $(2r)!$ denominator.
This real-even extraction does not itself assert that the entire dressed
function is even or real-valued for every time. No such symmetry theorem is
needed or claimed in this round.

`baseTwoCanonicalLogMoment` is the existing recurrence specialized to this
concrete phi, and `baseTwoCanonicalMomentSequence` is literally that sequence:

$$h_r=\frac{-(r+1)\phi_{r+1}-\sum_{j<r}h_j\phi_{r-j}}{\phi_0}.$$

Public theorems:

- `baseTwoCanonicalLogMoment_isSequence`;
- `baseTwoCanonicalLogMoment_unique`;
- `baseTwoCanonicalLogMoment_formal_logDerivative`:
  $\operatorname{mk}(h)\operatorname{mk}(\phi)=-\partial\operatorname{mk}(\phi)$;
- `baseTwoCanonicalLogMoment_unique_of_formal_identity`;
- `baseTwoCanonicalLogMoment_cutoff_independent`;
- `baseTwoCanonicalMomentSequence_eq_logMoment`.

Neither `cameraFactor`, `completion`, a freely supplied tail, nor a nonzero-phi
hypothesis is an input to the new canonical sequence. The general parametrized
ledger and `externalTail_changes_phi_zero` remain correct and unchanged.

## Strict status and remaining gates

`PASS_CANONICAL_DRESSING_MOMENTS` means only the concrete dressing/moment seam
above. The historical scalarization mismatch is REDUCED: arbitrary tail and
arbitrary dressing have disappeared from this canonical base-two path.
The independent modern depth-amplitude C2/Green source to this material-amplitude
observable crosswalk is still OPEN; the two amplitudes are not identified.

The next mathematical gate is an actual global orthogonal jet family whose
parity Gram equals these concrete moments:

$$h_{i+j}=\langle e_i,e_j\rangle,\quad
h_{i+j+1}=\langle o_i,o_j\rangle,\quad\langle e_i,o_j\rangle=0.$$

This includes the necessary provenance/readout and Taylor-jet-to-Green-jet
identification. Strict Hankel positivity additionally needs independence of
those jets. No positivity, Gram representation or independence is assumed or
proved here, and no Jacobi/global-height construction was changed.

Read-only next-round comparison at the same historical carry revision:
`GreenWronskianHankelBridge.lean` gives a generic conditional parity Gram kernel;
`CompletedNativeTfvdGreenMomentGramBridge.lean` still exposes a Taylor/forward-
difference Gram residual. Neither was imported and that residual was not
received as a hypothesis. The new local analytic signal and exact tail-jet
identity may help address it later; this round does not close it.

### Increment C verification and kernel certificate

Exit status 0:

- `lake build --wfail GeometryOfNumbers.Analysis.BaseTwoCanonicalDressingMoments`;
- `lake build --wfail GeometryOfNumbers.Analysis.BaseTwoCanonicalDressingMomentsAudit GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit`;
- `bash scripts/audit-analysis.sh`;
- `bash scripts/audit-foundation.sh`;
- `bash scripts/audit-geometry.sh`;
- `git diff --check` and new-source placeholder/trust-escape scan.

[Kernel certificate](CANONICAL_DRESSING_KERNEL_CERTIFICATE.json) records the
actual printed axiom list for all 49 public definitions/theorems across the
three modules, together with source SHA-256 hashes. Dedicated audits and
central Analysis Audit guard each name. All principal capstones below print
exactly `[propext, Classical.choice, Quot.sound]`:

| Capstone | Printed footprint |
| --- | --- |
| `baseTwoCanonicalCameraFactor_ne_zero` | standard three axioms |
| `baseTwoCanonicalCameraFactor_zero` | standard three axioms |
| `canonicalArchimedeanCompletion_analyticAt` | standard three axioms |
| `canonicalArchimedeanCompletion_zero_ne_zero` | standard three axioms |
| `baseTwoCanonicalResponse_analyticAt` | standard three axioms |
| `baseTwoCanonicalResponseSeries_eq_normalizedJets` | standard three axioms |
| `baseTwoCanonicalResponseSeries_coeff` | standard three axioms |
| `baseTwoCanonicalClosedResponse_eq` | standard three axioms |
| `baseTwoCriticalCompleteSignal_zero_re_pos` | standard three axioms |
| `baseTwoCanonicalPhi_zero_pos` | standard three axioms |
| `baseTwoCanonicalLogMoment_isSequence` | standard three axioms |
| `baseTwoCanonicalLogMoment_unique` | standard three axioms |
| `baseTwoCanonicalLogMoment_formal_logDerivative` | standard three axioms |
| `baseTwoCanonicalLogMoment_unique_of_formal_identity` | standard three axioms |
| `baseTwoCanonicalLogMoment_cutoff_independent` | standard three axioms |

No dependency configuration or Foundation/Geometry/R2/finite-height module
was changed. No zero table, numerical argument, zeta/RH/HP premise, imported
historical certificate, Hankel positivity or Gram representation occurs in
these proofs. Increment C is published under the commit subject
`feat: close canonical dressed response and unique concrete moments`.

## Published increments and final main check

Each mathematical increment was built, audited, kernel-guarded, committed,
pushed on the dedicated branch, fast-forwarded into main, pushed again and
verified against the GitHub remote before the next increment began.

| Increment | Mathematical publication commit | HEAD/main/origin/main/GitHub after integration |
| --- | --- | --- |
| A: exact camera germ | `3c0010f87afec21356df7af563ac8a5de72d856c` | all equal |
| B: explicit archimedean germ | `6d8010685ddcb191f267820b0aacfecbe7078f62` | all equal |
| C: analytic response, nonzero phi, concrete unique moments | `5335306a9d3ec3ea36cf18f3bfc80c166b94019a` | all equal |

On main at the third mathematical publication: all three proof modules,
all three dedicated audits, Analysis and central Audit built together with
`--wfail`, exit 0. The concrete-moment audit was additionally rerun with
`lake env lean`, exit 0. The certificate source hashes and all 49 printed
footprints were verified against main. Working tree was clean and the
GitHub `refs/heads/main` value equaled all local refs. This final publication
record is documentation only; it introduces no new mathematical claim.

Final strict status: `PASS_CANONICAL_DRESSING_MOMENTS`.
Arbitrary tail, arbitrary cameraFactor, arbitrary completion and a received
phi(0)-nonzero hypothesis are absent from the concrete base-two path.
The modern-source/observable crosswalk and actual global parity-jet Gram
representation remain open; historical scalarization mismatch is REDUCED.
