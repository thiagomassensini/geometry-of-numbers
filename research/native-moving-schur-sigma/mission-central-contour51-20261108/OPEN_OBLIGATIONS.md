# Open obligations — radius-51 contour route

## Provenance invariant

All moments remain the original C2 moments:

`geometric bracket → Genuine → native scalar N → F=A*N → R=-F'/(2F) → completedSigmaLogJet 0 n → H_n → Hankel`.

The ten zeros only define the comparison power sums `P_n`; they never define or replace `F`, `R`, or `H_n`.

## Remaining checkpoints

- [x] C1: classify every zero of the original entire continuation in `|z|≤51`, prove the twenty listed roots simple using the count with multiplicity, and exclude zeros on `|z|=51`.
- [x] C2: normalize the original jets and prove the finite residue identity for every `n`; the Lean theorem gives the paired ten-mode formula and records the contour orientation and normalization without Hadamard factorization. See `C2_RESIDUE_REDUCTION.md`.
- [x] C3 external certificate: the full circle is rigorously bounded by `|R|<4/5` in the Arb interval certificate `C3_ARb_CERTIFICATE.md`, with all 512 arc enclosures in `evidence/C3_ARb_ARCS.csv`. This certificate is not formalized in Lean.
- [x] C4: the Lean theorem deriving the uniform `C=40` tail from a contour identity and the circle bound is complete. C2 now supplies the former as a theorem; the circle bound remains computer-assisted evidence, not a Lean input yet.
- [x] C5 external interval computation: rigorous Arb enclosures give positive rational lower margins for all six original-source residuals. Their inclusion in the Lean contour integrals remains open; do not treat the conditional hypothesis as discharged.
- [x] C6: the four exact rational strict margins and B1 large-order implication are proved in Lean. The generic gate keeps decomposition, scale boxes, tail, and signs explicit; the new source-level wrapper discharges the decomposition and boxes and leaves the circle bound and residual signs visible.

The new `SigmaContour51SourceTail.lean` specializes these generic results to the original completed
characteristic. It derives the source decomposition and scale boxes from the fixed C2 root list and
proves the all-window conclusion conditional only on the C3 circle norm bound and the six central
signs. Those Lean hypotheses are not discharged by the external Arb runs. `SigmaContour51BoxSensitivity.lean` now
formalizes the exact C5 source specialization at `d=0`: the displaced product is the square of
`completedNativeOperatorCharacteristic`, which equals the square of
`completedNativeCharacteristicContinuation` under the explicit genuine-strip condition; the source
log-derivative coefficients are `2*completedSigmaLogJet 0 n`, and `e_n` is half that source moment
minus the ten-mode power sum. This algebraic identity does not move any C5 interval enclosure from
`d=99/2000` or `d=1/10`; a quantitative displacement enclosure or a direct central source
evaluation is still required.

The same module proves the first-window gate `completedNative_sigmaPadeD_zero_pos_of_contour51_bound`:
once the circle bound is supplied, only `e_0≥0` and `e_2≥0` are required; `e_1` is bounded in
absolute value and no sign assumption on it is made. The minimal first-window inputs still to prove
from the original source using this route are therefore the Lean circle bound plus those two
residual signs. A second gate in `SigmaContour51ArbResidualGate.lean` is sharper for the available
certificate: it proves the first determinant from two-sided source intervals for `e_0,e_1,e_2`,
without a global circle bound. Its exact rational determinant margin is proved in Lean, but the
interval-to-integral transfer remains a hypothesis.

## Current mathematical limits

The older numerical contour and Taylor probes use 65-digit mpmath arithmetic and a finite mesh; they remain diagnostics only. Separate from them, C3 has rigorous external Arb certificates for the circle bound and two-sided intervals of the first six C2 residual integrals, with exact rational endpoints and positive lower margins in `C3_ARb_CERTIFICATE.md`. Neither certificate has been imported or re-proved in Lean. The exact open hypotheses are: (1) a Lean proof that the 512-arc Arb enclosures imply the circle bound required by C4, including transport of the classical completed-zeta logarithmic derivative to the derivative of the Lean continuation; (2) a Lean proof that the 4096-arc Arb ranges enclose the lower-path integrals in `contour51ArbLowerPathResidualIntervalBounds`; (3) no additional analytic or sign hypotheses beyond those explicit inputs for the conditional all-window theorem. The full-circle parameterization, orientation, response oddness, quotient evenness, path scaling, and integrability from C1's zero-free boundary are now proved in `SigmaContour51ArbContourBridge.lean`; derivative/log-derivative transport to the Arb evaluator and interval-arithmetic transfer of complete-arc ranges remain. The first `s=0` theorem needs only the first three two-sided path inclusions. C5 displaced boxes at nonzero `d` remain distinct; no Bernoulli table or full zeta/Gamma node certificate was duplicated.

The strict rational lower margins available for `e_0,…,e_5` are, respectively,
`9/1000`, `9/10000000`, `9/50000000000`, `1/25000000000000`,
`1/100000000000000000`, and `1/500000000000000000000`. Until the lower-path interval
proposition is proved from the Arb arc data, these are verified comparisons against external
endpoints, not Lean signs for `e_n`. The next minimal lemma for an unconditional first advance is
`contour51ArbFirstThreeLowerPathResidualIntervalBounds`; it yields the compiled bound
`1/1000000000 < sigmaPadeD 0 0` without the global circle estimate.
