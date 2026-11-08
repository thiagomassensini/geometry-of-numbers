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

The older numerical contour and Taylor probes use 65-digit mpmath arithmetic and a finite mesh; they remain diagnostics only. Separate from them, C3 has rigorous external Arb certificates for the circle bound and two-sided intervals of the first six C2 residual integrals, with exact rational endpoints and positive lower margins in `C3_ARb_CERTIFICATE.md`. Neither certificate has been transferred to a Lean theorem. The exact open inputs are:

1. **Uniform circle bound:** prove in Lean that the 512-arc Arb enclosures imply `‖R z‖≤4/5` for every `‖z‖=51`, including validated Taylor/Cauchy remainders and their pointwise inclusion in the original response. `contour51OriginalResponse_eq_arb_formula_lower_path` now supplies the formal source evaluator on the lower semicircle; oddness handles the upper half. This is the `hR` input to C4.
2. **Six residual intervals:** prove `contour51ArbLowerPathResidualIntervalBounds`, namely the lower and upper rational endpoint inequalities for each original lower-path integral `n≤5`, from all 4096 complete-arc Arb ranges. The explicit source evaluator and its domain conditions are proved for every lower-path point. The new Lean theorem `contour51_intervalIntegral_bounds_of_uniform_partition` discharges the exact integration step conditional on pointwise arc enclosures and rational weighted-sum comparisons. Still open are the complete-arc evaluator inclusions (including Taylor/Cauchy remainders) and verification that their weighted endpoint sums imply the six stored rational endpoints.
3. **First unconditional advance:** only the first-three version for `n=0,1,2` is needed by `completedNative_sigmaPadeD_zero_pos_of_contour51_lower_path_intervals`; it yields the strict absolute margin `1/1000000000 < sigmaPadeD 0 0`.

The source differential identity and its explicit evaluator expansion are now compiled; `contour51OriginalResponse_eq_arb_formula_lower_path` proves the exact formula at every `u∈[0,1]`, with `F(z)≠0`, `0<Re(s)`, and `s≠1` discharged from C1 and the path geometry. Zeta nonvanishing follows from source nonvanishing and the exact factorization. The original full-circle parameterization, orientation, oddness/evenness, lower-path identity, and integrability are also compiled. The remaining residual gap is the complete-arc evaluator/remainder transfer and exact comparison of its weighted rational sums with the stored endpoints; the interval integration step between those facts and the path integral is now a Lean theorem. For all-window positivity, there are no hidden premises beyond `hR` and all six residual intervals (equivalently the six signs in the separate source-tail theorem). The first-window gate uses only the first three two-sided intervals, without `hR` or a sign premise on a remainder. C5 displaced boxes at nonzero `d` remain distinct; no Bernoulli table or full zeta/Gamma node certificate was duplicated.

The strict rational lower margins available for `e_0,…,e_5` are, respectively,
`9/1000`, `9/10000000`, `9/50000000000`, `1/25000000000000`,
`1/100000000000000000`, and `1/500000000000000000000`. Until the lower-path interval
proposition is proved from the Arb arc data, these are verified comparisons against external
endpoints, not Lean signs for `e_n`. The next minimal lemma for an unconditional first advance is
`contour51ArbFirstThreeLowerPathResidualIntervalBounds`, using the now-compiled original-source
evaluator identity on the path and its remaining arc inclusion/remainder proof; it yields the compiled bound
`1/1000000000 < sigmaPadeD 0 0` without the global circle estimate.
