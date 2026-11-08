# Open obligations — radius-51 contour route

## Provenance invariant

All moments remain the original C2 moments:

`geometric bracket → Genuine → native scalar N → F=A*N → R=-F'/(2F) → completedSigmaLogJet 0 n → H_n → Hankel`.

The ten zeros only define the comparison power sums `P_n`; they never define or replace `F`, `R`, or `H_n`.

## Remaining checkpoints

- [ ] C1: classify every zero of the original entire continuation in `|z|≤51`, prove the twenty listed roots simple using the count with multiplicity, and exclude zeros on `|z|=51`.
- [ ] C2: normalize the original jets and prove the finite residue identity for every `n`; verify origin and paired-root residues, contour orientation, and `2πi` factors without Hadamard factorization.
- [x] C3: the full circle is rigorously bounded by `|R|<4/5` in the Arb interval certificate `C3_ARb_CERTIFICATE.md`, with all 512 arc enclosures in `evidence/C3_ARb_ARCS.csv`. This is not yet formalized in Lean.
- [ ] C4: derive the uniform `C=40` tail from the contour estimate and the radius conversion.
- [ ] C5: rigorously prove the six original-source inequalities `e_0,…,e_5≥0`; do not infer them from a global zero-location assertion or assume positivity of the Hankel minors.
- [ ] C6: formalize the four exact rational strict margins and combine them with B1's large-order theorem only under every remaining analytic premise.

## Current mathematical limits

The numerical contour and Taylor probes use 65-digit mpmath arithmetic, a finite mesh, and `mp.zetazero` only for subtracting the ten comparison powers. They do not certify an interval between mesh nodes, a sign, a root count, or an analytic remainder. The PR #306 rational gate uses Python `Fraction`; it still needs a Lean proof.
