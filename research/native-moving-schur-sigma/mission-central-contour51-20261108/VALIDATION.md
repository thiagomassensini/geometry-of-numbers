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
- No C2/C3 rebuild was run. C5 and other Luna worktrees/caches were not used as build outputs.

## Investigation source identity

- Copied `RESEARCH.md` blob SHA-1: `be54ffdc43332c962aba914e18cc3fa07b4a9c4e`; the local copied file has the same Git blob SHA.
- Copied `reproduce.py` blob SHA-1: `b286f6b9c01d55e94dac4235f174b914163ce093`; the local copied file has the same Git blob SHA.
- Reproduction command: `python3 research/native-moving-schur-sigma/mission-central-contour51-20261108/reproduce.py`.
- Reproduction output: `evidence/PR306-reproduce.log`; SHA-256 `574b43aa21bf2e0f8b3c72c64da6c1ca888069cd85088916107db6140f803bfd`.
- The rerun produced the recorded sample maximum `0.634520221651175412`, sample mean `0.569580198724316508`, and positive floating-point residual probes `e_0,…,e_5`. This is only a consistency check of the experiment; it does not certify any continuum bound or sign.

## Required provenance sources inspected

- `SigmaNativeContinuation.lean`: `completedNativeCharacteristicContinuation` is the existing regularized-completed-zeta expression in `operatorHeightParameter`; its analyticity, evenness, and equality to the native characteristic on the native strip are explicit.
- `SigmaHeight50Integration.lean` and B2's `SigmaCentralTenHeightRootBridge.lean`: the same ten heights and positive/negative root statements come from B2; the moments are not rebuilt from zeros.
- `RHHeight.Main`: `rh_up_to_height_fiftytwo`, `low_height`, and `ncount_three_fiftytwo` are imported from the existing compiled certificate. `RHHeight.Skeleton.mem_and_simple_of_Ncount_le` converts the multiplicity-weighted count into exact membership and simplicity once ten distinct roots are supplied.
- C1 must use `Ncount` with multiplicity, not B2's distinct-point count alone.

## C1–C6

Pending. Record each Lean command, successful and failed logs, theorem axioms, and source/OLean/log hashes at the checkpoint where they are obtained. Keep experimental claims separate from formal results.
