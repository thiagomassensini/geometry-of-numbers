# Canonical moments and the actual Green parity Gram

## Increment A — neutral parity mathematics

Starting main: `9d6b687cc7a2b7d57e37c94cc644f1a79696ff0f`.
The concrete sequence remains the already-published
`BaseTwoCompletion.baseTwoCanonicalMomentSequence`, with no free tail or dressing.

The question is whether its moments are the inner products of one existing
geometric Green/Parseval jet family. A Gram of the scalar response, or vectors
constructed from Hankel/Cholesky, would reverse the required provenance and
does not answer this question.

`ParityMomentGram.lean` defines the neutral kernel on `ℕ ⊕ ℕ`:

$$K(e_i,e_j)=h_{i+j},\qquad K(o_i,o_j)=h_{i+j+1},\qquad K(e_i,o_j)=0.$$

`IsParityMomentGramRepresentation` states equality with the Gram of an existing
family. It does not construct that family. The public implications are:

- `parityMomentGram_even`: existing unshifted representation;
- `parityMomentGram_odd`: existing shifted representation;
- `parityMomentGram_even_odd_orthogonal`: mixed inner products vanish;
- `hankelPair_posSemidef_of_parityMomentGram`: both sections PSD at every N;
- `hankelPair_posDef_of_parityMomentGram`: both sections PD when their two
  finite prefixes are independently linearly independent.

These are generic theorems, not unconditional positivity results for the
canonical sequence. The actual first column, complete two-variable kernel and
independence remain separate obligations. No field asserting any of those
obligations is added to a source structure.

## Provenance and the next inspection

The local source `c2GlobalGreenInputIsometry t V` lives in
`GreenFrame.Concrete.State`; its Parseval image lives in `ConcreteAnalysisSpace`.
The source has decoded C2 depth amplitude `2^(-k/2)` and material phase
`exp(-it log n)`. The synthesized material observable instead has amplitude
`n^(-1/2)`. No pointwise identification of these amplitudes is made.

The local complete-signal and response analyticity concern a scalar-valued
function. They do not themselves provide a boundary/readout identity on the
Green carrier or all-order Hilbert-domain control for arbitrary CoreState.
The next inspection must identify that vector readout before comparing jets.

Historical comparison is read-only, at carry-self-adjoint-operator revision
`62b1c0d6b18e70b4c156c3bdf0253893fdb27a35`:
`GreenWronskianHankelBridge`, `C2GeometryNativeSourceBridge`,
`CompletedNativeTfvdGreenMomentGramBridge`, `CompletedNativeGreenWeylHeight`.
The historical first-column and Taylor/forward-difference premises are not
accepted as hypotheses for a concrete local result. No historical package is
imported, and no height operator is constructed.

## Verification ledger

The dedicated audit and central Analysis audit guard all seven new public
names and print their transitive axioms. The allowed set is
`propext`, `Classical.choice`, `Quot.sound`. Build/audit exit statuses and the
publication commit will be recorded after validation. Foundation, Geometry,
R2, dependencies and existing canonical moment statements are unchanged.

Increment A validation: final builds with `--wfail` of ParityMomentGram,
ParityMomentGramAudit, Analysis and central Audit all exit 0. All three
`bash scripts/audit-{analysis,foundation,geometry}.sh` checks exit 0;
`git diff --check` exits 0 after removing one trailing blank line.
All five new theorem footprints print exactly
`[propext, Classical.choice, Quot.sound]`; the two definitions also pass the
rejecting guard. No forbidden proof declaration appears in the new modules.
The original checkpoint is clean and no parallel changes were included.


## Increment B — actual full vector orbit, exact transport, explicit gates

Increment A was integrated and pushed as
`4c2f51828cac07edeec10cd0d76621ddfb320c10` before this block began.

### Carrier and definitions before comparison

The carrier is the **existing** `GreenFrame.Concrete.State`, and after P the
**existing** `ConcreteAnalysisSpace`. Let

$$f_V(t)=\texttt{c2GlobalGreenInputIsometry}\ t\ V,\qquad
P=\texttt{greenParsevalAnalysis}.$$

The input V is the existing CoreState argument of this source. No core vector
is selected to fit moments. No new Hilbert space, Cholesky vectors or scalar
response Gram is constructed. The diagnostic orbit coefficients are

$$j_r(V)=\frac{\partial_t^r f_V(0)}{r!},\qquad
\widehat j_r(V)=\frac{\partial_t^r(P f_V)(0)}{r!}.$$

Names: `c2MaterialOrbitJet`, `c2ParsevalOrbitJet`.
They retain all material coordinates and all Parseval channels. They are
**orbit coefficients**, not an asserted realization of the desired completed
boundary/Green-Wronskian jet. Both definitions use Mathlib's total iterated
derivative; outside the smooth regime this is a formal total value, not an
analytic/Taylor certificate. No regularity of an arbitrary core state is claimed.

### What is proved for the same P

`greenParseval_differentiableAt_iff` and `greenParseval_contDiffAt_iff`
show that applying P preserves **and reflects** vector regularity, at every
specified order. P† is a bounded left inverse. In the non-differentiable case,
both total first derivatives vanish by Mathlib's convention. Induction then
proves `greenParseval_iteratedDeriv` without hiding a domain hypothesis.
In the regular regime this is the actual iterated derivative transport.

`c2ParsevalOrbitJet_eq_transport` proves

$$\widehat j_r(V)=P j_r(V).$$

`greenParseval_inner_real` and `c2ParsevalOrbitJet_inner` prove

$$\langle\widehat j_r(V),\widehat j_q(V)\rangle_{\mathbb R}
=\langle j_r(V),j_q(V)\rangle_{\mathbb R}.$$

`greenParseval_parityMomentGram_iff` says that P neither creates nor removes a
parity moment Gram representation of a supplied **existing vector** family.
This equivalence does not instantiate the premise for the canonical moments.

### Domain gate is not bypassed

`c2ParsevalOrbit_differentiableAt_zero_iff_log_moment` proves exactly

$$\operatorname{DifferentiableAt}_0(P f_V)
\iff\sum_n(\log n)^2\operatorname{normSq}(f_V(0)(n))<\infty,$$

where the right side is formally `Summable` of the nonnegative sequence.
`c2ParsevalOrbit_contDiffAt_iff` preserves the all-order Hilbert gate too;
it does not discharge it. Neither unbounded clock powers nor a universal
analytic-vector assertion is used. Analyticity of the separate scalar response
cannot replace this vector regularity condition.

### First column: named residual, not a zero hypothesis

The directly available orbit candidate is

$$C_V(p)=\langle\widehat j_{2p}(V),\widehat j_0(V)\rangle_{\mathbb R}.$$

`c2ParsevalOrbitFirstColumn` defines this diagnostic readout **after** the full
vector transport. It is not designated the correct completed boundary column.
`baseTwoCanonicalGreenFirstColumnResidual` records

$$\mathcal R_V(p)=C_V(p)-\texttt{baseTwoCanonicalMomentSequence}(p).$$

`baseTwoCanonicalGreenFirstColumnResidual_eq_material` proves exactly

$$\mathcal R_V(p)=\langle j_{2p}(V),j_0(V)\rangle_{\mathbb R}-h_p.$$

Thus the Parseval step alone cannot kill this residual. It does not follow
that no other legitimate synthesized boundary readout can identify the moments.
No residual-zero premise is added, no normalization is fitted, and no moments
are used to choose or manufacture V or its coefficients.

`c2ParsevalOrbitFirstColumn_zero` and
`baseTwoCanonicalGreenFirstColumnResidual_zero` give the exact anchor

$$C_V(0)=\|V\|^2,\qquad\mathcal R_V(0)=\|V\|^2-h_0.$$

This is an audit identity, not a claim that h0 equals 1, is negative, or disagrees
with every possible geometric boundary readout. No numerical value is used.

## Precise first unresolved seam

**`PASS_PARITY_GRAM_TRANSPORT_FIRST_COLUMN_OPEN`** is the round status.
Neither full canonical Gram PASS nor LI-open Gram PASS is claimed.

The local complete-signal synthesis gives a scalar material-amplitude bracket
signal, its concrete dressing and its log-derivative moments. The local full
C2/Green/Parseval synthesis gives a depth-amplitude vector orbit. No local
typed completed/dressed **vector boundary readout** currently identifies these
as readouts of the same synthesis, or identifies its first column with h_p.
The readout equation must be derived before its Taylor coefficients can be
compared. The newly proved scalar all-order identities do not supply that
missing vector equality.

The historical `canonicalC2Geometry_seededClockFirstColumn_eq_cameraPolarizedMoment`
receives `HasCorrectedNativeSeededClockBoundaryTransport`; the full historical
kernel theorem receives the same premise. The historical Taylor/forward-
difference bridge receives factor Green representations, a normalized kernel
certificate and a residual-zero premise. None is an unconditional local
solution, and none is ported as an assumption. The historical height certificate
is likewise not a proof source for any local moment representation.

What is closed: neutral parity implications and exact all-order Parseval
transport of the already-existing orbit, pairings, regularity gates and
first-column residual. What is **not** closed: the correct completed vector
boundary column, its equality with h, propagation to the full canonical parity
kernel, concrete mixed orthogonality, all-order canonical Hankel PSD,
even/odd LI or PD. There is therefore no justified unique final operator gate:
first-column/readout identification comes first; its vector regularity and
transport, then independence, still need their own proofs.

The Taylor↔Green **moment** residual has not been eliminated. This is not a
no-go for the complete theory or for a future fully synthesized readout.
No identification `n^(-1/2)=2^(-k/2)` occurs, and no scalar response is embedded
as an artificial one-dimensional Gram carrier.

## New public theorem ledger

- `greenParseval_differentiableAt_iff`
- `greenParseval_deriv`
- `greenParseval_iteratedDeriv`
- `greenParseval_contDiffAt_iff`
- `greenParseval_inner_real`
- `greenParseval_parityMomentGram_iff`
- `c2ParsevalOrbitJet_eq_transport`
- `c2ParsevalOrbitJet_inner`
- `c2ParsevalOrbit_differentiableAt_zero_iff_log_moment`
- `c2ParsevalOrbit_contDiffAt_iff`
- `c2ParsevalOrbitFirstColumn_eq_material`
- `baseTwoCanonicalGreenFirstColumnResidual_eq_material`
- `c2ParsevalOrbitFirstColumn_zero`
- `baseTwoCanonicalGreenFirstColumnResidual_zero`

All public definitions and theorems receive rejecting guards and `#print axioms`
in the dedicated and central audits. Final verification and publication are
recorded below after execution.

## Increment B executed validation

Every one of the 18 new public definitions/theorems printed exactly
`[propext, Classical.choice, Quot.sound]` and passed the rejecting guard.

| Command | Exit |
|---|---:|
| `lake build --wfail GeometryOfNumbers.Analysis.CanonicalGreenMomentJetSeam` | 0 |
| `lake build --wfail GeometryOfNumbers.Analysis.CanonicalGreenMomentJetSeamAudit GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit` | 0 |
| `bash scripts/audit-analysis.sh` | 0 |
| `bash scripts/audit-foundation.sh` | 0 |
| `bash scripts/audit-geometry.sh` | 0 |
| `git diff --check` | 0 |

The four new Lean modules have no forbidden proof declarations.
All 19 new public theorems from increments A/B are guarded and kernel checked.
Only the round files were staged; the canonical checkpoint was initially clean.
No dependencies, Foundation, Geometry, R2 or existing moment definitions changed.

## Publication ledger and final scope

| Increment | Integrated main / GitHub SHA | Build, audits, kernel guards |
|---|---|---|
| A: neutral parity Gram | `4c2f51828cac07edeec10cd0d76621ddfb320c10` | PASS, all exit 0 |
| B: actual orbit jet transport and first-column seam | `d4d07ac6c7c0b8c48c2f7989de2fea26ead58ea5` | PASS, all exit 0 |

For each mathematical increment, the dedicated branch was committed and
pushed, main was fast-forwarded and pushed, then HEAD/main/origin-main and
`git ls-remote origin refs/heads/main` were checked equal before the next block.
Both mathematical increments are already in main. This final documentation
ledger is published by the same branch/fast-forward sequence.

Final mathematical status: `PASS_PARITY_GRAM_TRANSPORT_FIRST_COLUMN_OPEN`.
The requested concrete canonical moment Gram is not yet proved.
No unconditional canonical Hankel positivity or jet independence is asserted.
The existing concrete moments, canonical dressing, complete tail and source
provenance statements remain unchanged. The next required proof is a typed
completed vector boundary/readout identity giving the canonical first column;
regularity, two-variable transport and independence cannot be replaced by a
residual-zero hypothesis. Work stops before any global height construction.
