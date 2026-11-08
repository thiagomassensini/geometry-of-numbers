# Validation ledger — radius-51 contour route

## C0 isolation and source audit

- `git fetch origin` completed before creating the new branch.
- PR #304: open/mergeable, base `main`, head `agent/c2-central-hankel2-allorder-20261107` at `6397f479f8c373b59cdffea512bbd8dd95b24fb3`.
- PR #311: open/mergeable, based on the B1 branch, head `agent/c2-central-ten-heights-b2-20261108` at `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`.
- PR #306: open/mergeable, base `main`, head `agent/c2-central-contour51-20261108` at `e96e3a132ee6c4f494fee97e3ff1753f606514fc`. Its two original files were read in full and copied byte-for-byte; the original PR branch was not checked out for writing or modified.
- New base commit: `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`.
- Worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108`.
- Branch: `agent/c2-contour51-20261108`.
- Exclusive Lean output: `/home/thlinux/tmp/c2-contour51-20261108-lean432`.
- Lean toolchain: `leanprover/lean4:v4.32.0`; local `lean --version` reports Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- Read-only imported build paths: C2 integration and external artifacts under `/home/thlinux/worktrees/geometry-of-numbers-sigma-c2-c3-main/research/native-moving-schur-sigma/.cache/c3-validation/c2/`; B2 output `/home/thlinux/tmp/c2-central-ten-heights-b2-20261108-lean432`; B1 rational-gate output `/home/thlinux/tmp/c2-central-hankel2-20261107-lean432`; Mathlib output `/home/thlinux/geometry-of-numbers/.lake/build/lib/lean`.
- The primary checkout was already dirty with unrelated untracked `GeometryOfNumbers/Analysis/IntegerMomentGramPositivity.lean` and `research/entrywise-moment-square/`; neither is in this worktree or included in this branch.
- No Lean C2/C3 rebuild was run. The C3 Arb script was executed in this worktree and its own evidence files. C5 and other Luna worktrees/caches were not used as build outputs.

## Investigation source identity

- Copied `RESEARCH.md` blob SHA-1: `be54ffdc43332c962aba914e18cc3fa07b4a9c4e`; the local copied file has the same Git blob SHA.
- Copied `reproduce.py` blob SHA-1: `b286f6b9c01d55e94dac4235f174b914163ce093`; the local copied file has the same Git blob SHA.
- Reproduction command: `python3 research/native-moving-schur-sigma/mission-central-contour51-20261108/reproduce.py`.
- Reproduction output: `evidence/PR306-reproduce.log`; SHA-256 `574b43aa21bf2e0f8b3c72c64da6c1ca888069cd85088916107db6140f803bfd`.
- The rerun produced the recorded sample maximum `0.634520221651175412`, sample mean `0.569580198724316508`, and positive floating-point residual probes `e_0,…,e_5`. This is only a consistency check of the experiment; it does not certify any continuum bound or sign.

## C3 Arb interval certificate

- Certificate: `C3_ARb_CERTIFICATE.md`; implementation: `certify_contour51_bound.py`; per-arc interval enclosures: `evidence/C3_ARb_ARCS.csv`.
- Command: `python research/native-moving-schur-sigma/mission-central-contour51-20261108/certify_contour51_bound.py --csv research/native-moving-schur-sigma/mission-central-contour51-20261108/evidence/C3_ARb_ARCS.csv`.
- Environment: Python 3.12.12, python-flint 0.8.0, 160-bit Arb precision, 512 rational arcs, Taylor degree 32.
- Result: maximum certified `|xi'/xi| < 1.492825`, hence maximum `|R| < 0.746413 < 4/5`; minimum certified `|zeta|` lower bound `>0.942660`. The script checked the Taylor-domain pole exclusion and every arc inequality.
- Proof boundary: this is a rigorous computer-assisted Arb certificate, not a Lean theorem. The C4 Lean theorem still takes the circle bound/identity as explicit hypotheses.
- SHA-256: script `ab18a38e9fcbf0eeebb27f047e81b2ec65f4816d70feae741e4f4007bed157ff`; certificate note `2c3a7dee8f9ba7514596c94a152843fb74907904833d686a9761f76060654690`; arc CSV `c1a2a37fcd1450c34181edd0f6fe7fac334fdf750be153d708c15f2e0fb90519`; run log `8e76addb77abdacf677b4e0a019b2e52bb86359f4172e1d4c8291b4eba868609`.

## Required provenance sources inspected

- `SigmaNativeContinuation.lean`: `completedNativeCharacteristicContinuation` is the existing regularized-completed-zeta expression in `operatorHeightParameter`; its analyticity, evenness, and equality to the native characteristic on the native strip are explicit.
- `SigmaHeight50Integration.lean` and B2's `SigmaCentralTenHeightRootBridge.lean`: the same ten heights and positive/negative root statements come from B2; the moments are not rebuilt from zeros.
- `RHHeight.Main`: `rh_up_to_height_fiftytwo`, `low_height`, and `ncount_three_fiftytwo` are imported from the existing compiled certificate. `RHHeight.Skeleton.mem_and_simple_of_Ncount_le` converts the multiplicity-weighted count into exact membership and simplicity once ten distinct roots are supplied.
- C1 must use `Ncount` with multiplicity, not B2's distinct-point count alone.

## C1–C6

C1 source is drafted in `SigmaContour51DiskBridge.lean` but remains uncompiled. C2's generic local-residue theorem is drafted in `SigmaContour51Residue.lean`; `C2_RESIDUE_REDUCTION.md` records the normalization and finite Cauchy route, including the unformalized analytic extension/gluing step. C4's conditional normalized-integral bound and exact radius conversion, plus C6's rational margins and conditional closure, are drafted in `SigmaContour51RationalGate.lean`, also uncompiled. At the last resource check, external C5 process PID `108950` was still active in its own worktree, so no Lean build was started here. Recheck before compiling. Record each Lean command, successful and failed logs, theorem axioms, and source/OLean/log hashes at the checkpoint where they are obtained. Keep experimental claims separate from formal results.
