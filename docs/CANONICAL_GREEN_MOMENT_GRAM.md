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
