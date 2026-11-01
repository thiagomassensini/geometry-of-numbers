# Seventh odd canonical source (K7) investigation report

## Scope and constraints

- Repository: `/home/thlinux/worktrees/geometry-of-numbers-k7`
- Branch: `k7-odd-canonical-source`
- Baseline commit: `190ea84` (capstone E8/E12 baseline preserved in separate worktree)
- This mission did not modify Theta16 Aggregator files in `carry-self-adjoint-operator`.

## Files inspected

Requested targets were inspected directly:

- `research/seventh-even-centered-source/`
  - `EvenSeventhCertificate.lean`
  - `Regression.lean`
  - `CenteredMomentBoxes.lean`
  - `SourceCoefficients.lean`
  - `CenteredEvaluation.lean`
  - `RelativeResidual.lean`
- `research/sixth-odd-twelve-sources/`
  - `OddTrialPositivity.lean`
  - `OddTrialData.lean`
  - `OddSourceBoxes.lean`
  - `OddOrderedCertificate.lean`
  - `OddPhysicalTwelve.lean`
- `research/theta-fifth-odd-pattern/TenSourceReturn.lean`
- `research/theta-fifth-odd-pattern/AllOrderPattern.lean`
- `research/structural-native-krylov-gap/`
  - `CanonicalClockGap.lean`
  - `Regression.lean`
- `/home/thlinux/carry-self-adjoint-operator/CarrySelfAdjointOperator/NativeSourceAllOrderSchur.lean`

## Existence check: does K7 already exist?

### Search result

Searches for the target signatures and aliases found no existing theorem certifying:

- `0 < sourceMomentSchur h 1 6`
- `(sourceMomentMatrix h 1 7).PosDef`
- odd-seven analogs under names like `seventh_odd_*`

The repository currently certifies:

- even 7th block: `CarrySeventhEven.even_source_seven_posDef`
- even 7th pivot: `CarrySeventhEven.seventh_even_pivot_pos`
- odd 6th block: `CarrySixthOdd.odd_source_six_posDef`
- odd 6th pivot: `CarrySixthOdd.sixth_odd_pivot_pos`

No K7 certificate under alternative nomenclature was found.

## Obligation mapping (requested items)

### 1. Original expression of the pivot `sourceMomentSchur h 1 6`

From `NativeSourceAllOrderSchur.lean`:

- `sourceMomentSchur m s n := m (2*n+s) - b^T A^{-1} b`,
  where `A = sourceMomentMatrix m s n` and `b = sourceMomentCoupling m s n`.

Specialized to `m = h`, `s = 1`, `n = 6`:

- `sourceMomentSchur h 1 6 = h 13 - b^T A^{-1} b`
- `A(i,j) = h(i+j+1)` for `0 <= i,j < 6` (uses moments `h1..h11`)
- `b(i) = h(i+7)` for `0 <= i < 6` (uses moments `h7..h12`)
- direct term: `h13`

### 2. Canonical moments needed (including `h13`)

To evaluate/sign the odd seventh pivot in original coordinates, the data footprint is:

- matrix entries: `h1..h11`
- coupling vector: `h7..h12`
- Schur top term: `h13`

Equivalent gate routes also involve one higher coefficient order via recurrence:

- `nativeSourceSchurRemainder 1 6` includes coefficient index `c14`
- via theta identity, `c14` is tied to `sourceThetaIntegral 13`

### 3. Available theta identities and rational boxes

Existing exact identities:

- `sourceThetaIntegral_moments`
- `sourceCoefficient_theta`
- `sourceCoefficient_parity`
- `criticalMargin_iff_sourceTheta`
- `oddMargin_iff_upper_theta`
- `criticalMargin_iff_pivot`
- `sourceMomentMatrix_succ_posDef_iff`

Available boxed ingredients around current frontier:

- Odd chain (`sixth-odd-twelve-sources`):
  - `compactMomentBox` validated only up to index `< 12` (i.e., through `h11`)
  - `twelfthCoefficientBox` (for `c12`)
  - derived `eleventhMomentBox` (for `h11`)
- Even-centered chain (`seventh-even-centered-source`):
  - `compactMomentBox` validated up to index `< 13` (i.e., through `h12`)
  - `thirteenthCoefficientBox` (for `c13`)

No inspected module in this mission provided:

- a certified box for `h13`
- a certified box for `c14`
- an explicit certified bound for `sourceThetaIntegral 13`

### 4. Minimal missing sign inequality

With `odd_source_six_posDef` already available, the minimal missing inequality is exactly:

`sourceThetaIntegral 13 < 4 * (Nat.factorial 28 : R) * sourceCeiling 1 6`

By existing equivalences, this is equivalent to:

- `HasCriticalMargin 1 6`
- `0 < sourceMomentSchur h 1 6`
- `(sourceMomentMatrix h 1 7).PosDef`

So the open point is a single odd-step gate at `(s,n) = (1,6)`.

### 5. Can H7 centralization methods transfer to K7?

Short answer: partially in structure, not yet in available bounds.

What transfers:

- trial-matrix strategy (`trialMatrix_identity`, invertible transport)
- ordered-pivot extraction from PosDef blocks
- critical-margin equivalence chain

What blocks direct transport today:

- odd K7 needs one order higher (`h13` / equivalently `c14` or `sourceThetaIntegral 13`)
- current odd certificate infrastructure was built for K6 (`h11`, `c12` frontier)
- centered-even infrastructure reaches `h12`/`c13`, still one step short for the odd K7 pivot term

Conclusion: H7 centralization architecture is reusable, but the certified enclosure frontier must advance by one odd step before a faithful K7 closure is possible.

## Current status

- K7 not yet certified in kernel.
- Open theorem target remains:
  - `(sourceMomentMatrix h 1 7).PosDef`
- This report isolates the exact missing inequality and dependency frontier without launching a heavy theta-certificate campaign.

## Lean formalization added in this mission

File: `research/seventh-odd-canonical-source/K7PivotBridge.lean`

Kernel-checked declarations:

- `CarrySeventhOddCanonical.k7_pivot_formula`
- `CarrySeventhOddCanonical.k7_pos_iff_margin`
- `CarrySeventhOddCanonical.k7_pos_iff_theta_gate`
- `CarrySeventhOddCanonical.k7_matrix_posDef_iff_pivot`

These declarations do not prove `0 < sourceMomentSchur h 1 6`; they formalize the exact equivalence chain and isolate the single missing gate.

Audit file: `research/seventh-odd-canonical-source/Audit.lean`

`#print axioms` output for all four declarations is:

- `[propext, Classical.choice, Quot.sound]`

## Directed compile commands executed

The module was compiled directly with explicit dependency caches (no broad rebuild):

1. compile bridge
2. compile audit (`#check` and `#print axioms`)

Both completed successfully after fixing transitive LEAN_PATH entries.

### Notable compile obstacles resolved

During directed compile setup, transitive path gaps surfaced and were resolved without changing theorem content:

- missing package/cache entries such as `CPFormal`, `NativeCarryC3Crosswalk`, and operator-side `CarrySelfAdjointOperator` path exposure
- stale geometry package object path in operator cache (`CarryMaterialFourthPivot.olean`) avoided by prioritizing geometry root build cache
- matrix notation elaboration (`⬝ᵥ`) required opening `Matrix` notation scope in the bridge file
