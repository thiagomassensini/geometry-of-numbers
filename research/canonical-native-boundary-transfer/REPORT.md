# Capstone audit — canonical native boundary transfer

## Scope and preservation status

- Isolated worktree: `/home/thlinux/worktrees/geometry-of-numbers-canonical-capstone`
- Branch: `capstone-canonical-native-boundary-positivity`
- Aggregator process in `carry-self-adjoint-operator` was detected active during this audit and was not interrupted.
- While Aggregator is active, this stage performs source inspection and dependency audit only (no heavy concurrent build).

## Mandatory declarations verified in source

### Canonical sequence identification

File: `research/structural-native-krylov-gap/CanonicalClockGap.lean`

- `canonical_moments_eq_native`:
  - Statement: `baseTwoCanonicalMomentSequence = canonicalCompletedNativeLogDerivativeMoment`
  - Role: identifies the canonical moment sequence with the completed native log-derivative moments.
  - Namespace: `CarryStructuralKrylov`
  - Dependencies in file headers:
    - `OddSourceBoxes`
    - `GeometryOfNumbers.Analysis.MaterialClockKrylovGap`
    - `GeometryOfNumbers.Analysis.BaseTwoCanonicalDressingMoments`

### Sixth-order positivity certificates (H6/K6 source blocks)

File: `research/sixth-even-source-schur/SixthEvenCertificate.lean`

- `even_source_six_posDef`:
  - Statement: `(sourceMomentMatrix h 0 6).PosDef`
  - Namespace: `CarrySixthEven`

File: `research/sixth-odd-twelve-sources/OddTrialPositivity.lean`

- `odd_source_six_posDef`:
  - Statement: `(sourceMomentMatrix h 1 6).PosDef`
  - Namespace: `CarrySixthOdd`

### Seventh-even certificates

File: `research/seventh-even-centered-source/EvenSeventhCertificate.lean`

- `even_source_seven_posDef`:
  - Statement: `(sourceMomentMatrix h 0 7).PosDef`
- `seventh_even_pivot_pos`:
  - Statement: `0 < sourceMomentSchur h 0 6`
- Namespace: `CarrySeventhEven`

File: `research/seventh-even-centered-source/Regression.lean`

- `seventh_even_sourceRemainder_pos`:
  - Statement: `0 < nativeSourceSchurRemainder 0 6`
- Namespace: `CarrySeventhEven`

### Operator-side bridge declarations

File: `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/CompletedNativeChiralEvenBoundarySplit.lean`

- `nativeSourceFiniteBoundaryEnergy_even_split (n : ℕ) (x : Fin (2*n) → ℂ)`
  - Splits native finite boundary energy into even/odd parity quadratic forms.

File: `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/NativeSourceAllOrderSchur.lean`

- `nativeSourceSchurRemainder_eq (s n : ℕ)`
  - Identifies `nativeSourceSchurRemainder s n` with `c0 * sourceMomentSchur ... s n`.

## Explicit dependency chain for canonical H6/K6 positivity

The source-level H6/K6 positivity is already connected to canonical moments by:

File: `research/structural-native-krylov-gap/Regression.lean`

- `regression_H6_K6`:
  - `(hankelGram baseTwoCanonicalMomentSequence 6).PosDef ∧ (shiftedHankel baseTwoCanonicalMomentSequence 6).PosDef`
  - Proof uses `canonical_moments_eq_native`, then converts from
    - `CarrySixthEven.even_source_six_posDef`
    - `CarrySixthOdd.odd_source_six_posDef`.

So the canonical 6x6 pair is already certified in current sources.

## What is already derivable vs what is still missing

### Target E12

Wanted target:

- `∀ x : Fin 12 → ℂ, x ≠ 0 → 0 < nativeSourceFiniteBoundaryEnergy 12 x`

Current source status:

- parity split theorem exists (`nativeSourceFiniteBoundaryEnergy_even_split`)
- canonical 6x6 pair positivity exists (`regression_H6_K6`)

Remaining formal gap in this worktree:

- a local transfer theorem that instantiates the split at `n=6` and plugs the canonical 6x6 positive-definite pair directly into strict positivity of the two quadratic forms for nonzero parity phase.

This is a theorem-engineering gap, not a missing certificate gap for H6/K6.

### Target E8

Wanted target:

- `∀ x : Fin 8 → ℂ, x ≠ 0 → 0 < nativeSourceFiniteBoundaryEnergy 8 x`

Current source status:

- no explicit published theorem in the inspected set stating canonical 4x4 parity pair positivity directly.

Likely route:

- derive 4x4 positivity from certified 6x6 positivity by principal submatrix inheritance (or alternate existing 4x4 chain if present elsewhere), then apply the same `n=4` split transfer.

This still needs an explicit formal transport lemma in the capstone module.

### H7 vs K7 status

- Certified on even channel:
  - `even_source_seven_posDef`
  - `seventh_even_pivot_pos`
  - `seventh_even_sourceRemainder_pos`
- Missing in the inspected set:
  - odd seventh companion certificate (`sourceMomentMatrix h 1 7`).

Therefore, H7 has certified even progress; K7 remains the explicit missing channel for a symmetric seventh-order extension.

## Kernel-compilation evidence status in this stage

- Source declarations and namespaces were verified directly in Lean files.
- Existing evidence logs were found for key certificate files:
  - `research/sixth-even-source-schur/evidence/SixthEvenCertificate.log`
  - `research/sixth-odd-twelve-sources/evidence/OddTrialPositivity.log`
  - `research/seventh-even-centered-source/evidence/EvenSeventhCertificate.log`
- Because Aggregator is currently active, this stage did not run fresh heavy recompilation.

## Stage-1 deliverable conclusion

- The canonical identification and H6/K6 positivity chain are present and explicit.
- A focused transport module is still required to conclude strict positivity statements for `E12` (and then `E8`) in the exact boundary-energy form.
- H7 even channel is certified; K7 channel is the precise missing extension point.

## Stage-2 implementation (transport module authored)

New files added in this stage:

- `research/canonical-native-boundary-transfer/CanonicalBoundaryTransfer.lean`
- `research/canonical-native-boundary-transfer/Audit.lean`
- `research/canonical-native-boundary-transfer/compile_module.sh`

### Source provenance status

- GitHub branch `research/boundary-energy-e8-theta16` in the operator repo contains the parity file:
  - `CarrySelfAdjointOperator/CompletedNativeChiralBoundaryParityCoordinates.lean`
- Local checkout at `/home/thlinux/carry-self-adjoint-operator` does contain this file and it declares:
  - `nativeSourceBoundaryPhase_nonzero`
- The capstone module was updated to import this file explicitly.
- The worktree root `/home/thlinux/worktrees/geometry-of-numbers-canonical-capstone` does not contain a local `.lake` directory; the active Lean environment is the operator checkout at `/home/thlinux/carry-self-adjoint-operator/.lake`.
- The compile helper was hardened to fail early when `.lake` or dependency caches are missing, rather than guessing or reconstructing the environment.

### Implemented theorems

In `CanonicalBoundaryTransfer.lean`:

- `boundary_energy_pos_of_canonical_pair_posDef`
  - Fixed-order transfer theorem:
    - assumptions:
      - `(hankelGram canonicalCompletedNativeLogDerivativeMoment n).PosDef`
      - `(shiftedHankel canonicalCompletedNativeLogDerivativeMoment n).PosDef`
    - conclusion:
      - `∀ x : Fin (2*n) → ℂ, x ≠ 0 → 0 < nativeSourceFiniteBoundaryEnergy (2*n) x`.

- `nativeSourceFiniteBoundaryEnergy_pos_12`
  - Reuses `regression_H6_K6` (via `canonical_h6k6_posDef_native`) to instantiate the transfer at `n = 6`.

- `nativeSourceFiniteBoundaryEnergy_pos_8`
  - Derives the canonical `4×4` pair from the canonical `6×6` pair using principal submatrix inheritance:
    - `Matrix.PosDef.submatrix`
    - embedding `Fin.castLE : Fin 4 → Fin 6`.
  - Then instantiates the same transfer at `n = 4`.

### Audit anchors

In `Audit.lean`:

- `#check` anchors for the three public theorems.
- `#print axioms` anchors for kernel-level dependency tracking.

### Compile status

- Stage-2 code authoring completed.
- Fresh directed compile of `CanonicalBoundaryTransfer.lean` remains pending in this stage due the active Aggregator process policy (no competing heavy build while operator Aggregator is running).
- Helper script `compile_module.sh` is prepared with default operator root:
  - `/home/thlinux/carry-self-adjoint-operator`
- The worktree root `/home/thlinux/worktrees/geometry-of-numbers-canonical-capstone` has no local `.lake` directory; the active Lean toolchain cache is in `/home/thlinux/carry-self-adjoint-operator/.lake`.
- The actual `.olean` target directory `/home/thlinux/carry-self-adjoint-operator/.lake/build/research/canonical-native-boundary-transfer` is absent at runtime, so the script exits early without reconstructing unrelated caches.

### Static validation executed

Validated in the current session without starting a new heavy build:

- `bash -n research/canonical-native-boundary-transfer/compile_module.sh` → exit `0`
- `git diff --check` → exit `0`
- `bash research/canonical-native-boundary-transfer/compile_module.sh CanonicalBoundaryTransfer /home/thlinux/carry-self-adjoint-operator` → exit `2` with explicit message:
  - `ERROR: missing dependency cache /home/thlinux/carry-self-adjoint-operator/.lake/build/research/canonical-native-boundary-transfer; capstone compile aborted without reconstructing the full environment.`

This is the exact current compile status: static verification passed, and the script correctly refuses to start a fresh heavy build while the operator cache state is incomplete.
