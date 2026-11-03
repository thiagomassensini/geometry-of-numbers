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

## Mission 7 update: exact K7 gate and viability scan

### 1. Exact gate equivalence formalized (kernel-checked)

In `research/seventh-odd-canonical-source/K7PivotBridge.lean`, the gate was specialized to the exact requested inequality:

- `sourceThetaIntegral13_eq_theta26_theta28`
- `k7_pos_iff_theta26_theta28_gate`
- `k7_matrix_posDef_iff_theta26_theta28_gate`

These combine:

- `k7_matrix_posDef_iff_pivot`
- `k7_pos_iff_theta_gate`
- `sourceThetaIntegral_moments` at `d = 13`

and produce the exact statement:

`(sourceMomentMatrix h 1 7).PosDef ↔ 3024 * completedNativeThetaTailMoment 26 - completedNativeThetaTailMoment 28 < 4 * (Nat.factorial 28 : ℝ) * sourceCeiling 1 6`.

Audit (`research/seventh-odd-canonical-source/Audit.lean`) compiles and prints axioms for all new declarations; all remain `[propext, Classical.choice, Quot.sound]`.

### 2. Reuse of SourceTwentySix and T26 certified box

In `research/seventh-odd-canonical-source/K7ThetaBounds.lean`:

- `mem_thetaTwentySixBox_available` reuses `CarrySeventhEven.mem_thetaTwentySixBox`

So the certified T26 interval is reused without rebuilding certificates.

### 3. Extension check toward T28 (without heavy campaign)

The same tabled-theta method was tested directly at order 28:

- `mem_tabledTheta_upto_twentyEight (p ≤ 28)`
- `mem_tabledTheta_28`

Both compile. Therefore, at this stage, there is no immediate formal obstruction in the generic tabled method itself for `p = 28`.

What is still missing is a narrow explicit containment theorem analogous to `thetaTwentySixBox` for `T28`; the existing work reused tabled machinery but did not yet derive a dedicated tight `thetaTwentyEightBox` interval in this mission.

### 4. Lightweight numerical viability scan (exploratory only)

Using existing evidence JSON artifacts (no new theta campaign), a high-precision exploratory scan produced:

- `T26` certified interval (from `theta_boxes[26]`):
  - low `3.922763626395069796941801296419297318e-10`
  - high `3.922763626395118953651952950919634060e-10`
  - width `4.915671015165450033674148274165191060e-24`

- midpoint estimate for `sourceCeiling 1 6` from canonical reference moments/coefficients in preflight:
  - `sourceCeiling(1,6) ≈ 9.724693482688938608979912230170599603e-37`

- corresponding gate RHS midpoint:
  - `4*(28!)*sourceCeiling(1,6) ≈ 1.185978279117341180839606186106650877e-6`

- required `T28` threshold implied by the gate:
  - `T28 > 3024*T26 - RHS`
  - midpoint-T26 threshold `≈ 2.654415045353582501694560909955477307e-10`

- Schur-coupling stability proxy at midpoint moments (`A = sourceMomentMatrix h 1 6`):
  - `cond_2(A) ≈ 2.363501e+31`
  - `b^T A^{-1} b ≈ 6.193843423170420394387972292562674898e-33`

Interpretation: the gate appears numerically plausible with large apparent slack at midpoint values, but the Schur complement path is extremely ill-conditioned.

### 5. First real mathematical obstacle

The first decisive obstacle is not writing the exact equivalence (now done), but obtaining a rigorous sign-certified inequality under tight error control for:

- `sourceCeiling 1 6` (which depends on an ill-conditioned Schur coupling with inverse of the 6x6 odd prefix), and
- `T28` with a certified interval tight enough to preserve sign after coupling with the ceiling term.

Because of the conditioning level (`~1e31`), independent interval bounds for ingredients are likely too conservative; preserving correlation structure (as in centered evaluation workflows) is expected to be necessary for a robust formal closure.

### 6. Practical recommendation for next proof step

1. Produce a dedicated certified `thetaTwentyEightBox` (tight interval, same source and tails).
2. Build a correlated enclosure for `sourceCeiling 1 6` that tracks coupled errors through the Schur solve, instead of independent box propagation.
3. Only then attempt the final strict gate proof and derive `(sourceMomentMatrix h 1 7).PosDef`.
