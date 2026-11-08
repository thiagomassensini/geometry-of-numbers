# Open obligations — radius-51 contour route

## Provenance invariant

All moments remain the original C2 moments:

`geometric bracket → Genuine → native scalar N → F=A*N → R=-F'/(2F) → completedSigmaLogJet 0 n → H_n → Hankel`.

The ten zeros only define the comparison power sums `P_n`; they never define or replace `F`, `R`, or `H_n`.

## Remaining checkpoints

- [x] C1: classify every zero of the original entire continuation in `|z|≤51`, prove the twenty listed roots simple using the count with multiplicity, and exclude zeros on `|z|=51`.
- [x] C2: normalize the original jets and prove the finite residue identity for every `n`; the Lean theorem gives the paired ten-mode formula and records the contour orientation and normalization without Hadamard factorization. See `C2_RESIDUE_REDUCTION.md`.
- [x] C3: the full circle is rigorously bounded by `|R|<4/5` in the Arb interval certificate `C3_ARb_CERTIFICATE.md`, with all 512 arc enclosures in `evidence/C3_ARb_ARCS.csv`. This certificate is not formalized in Lean.
- [x] C4: the Lean theorem deriving the uniform `C=40` tail from a contour identity and the circle bound is complete. C2 now supplies the former as a theorem; the circle bound remains computer-assisted evidence, not a Lean input yet.
- [ ] C5: rigorously prove the six original-source inequalities `e_0,…,e_5≥0`; do not infer them from a global zero-location assertion or assume positivity of the Hankel minors.
- [x] C6: the four exact rational strict margins and B1 large-order implication are proved in Lean. The generic gate keeps decomposition, scale boxes, tail, and signs explicit; the new source-level wrapper discharges the decomposition and boxes and leaves the circle bound and residual signs visible.

The new `SigmaContour51SourceTail.lean` specializes these generic results to the original completed
characteristic. It derives the source decomposition and scale boxes from the fixed C2 root list and
proves the all-window conclusion conditional only on the C3 circle norm bound and the six central
signs. Those two obligations are not discharged here. The existing C5 signs at noncentral
displacements do not imply these central residual signs without a separate `d=0` transport proof.

The same module now proves the first-window gate `completedNative_sigmaPadeD_zero_pos_of_contour51_bound`:
once the circle bound is supplied, only `e_0≥0` and `e_2≥0` are required; `e_1` is bounded in
absolute value and no sign assumption on it is made. The minimal first-window inputs still to prove
from the original source are therefore the Lean circle bound plus those two residual signs.

## Current mathematical limits

The numerical contour and Taylor probes use 65-digit mpmath arithmetic, a finite mesh, and `mp.zetazero` only for subtracting the ten comparison powers. They do not certify an interval between mesh nodes, a sign, a root count, or an analytic remainder. C2's contour identity and C6's rational gates are now Lean theorems; the six original-source signs remain open, and the C3 interval certificate has not yet been imported or re-proved in Lean.
