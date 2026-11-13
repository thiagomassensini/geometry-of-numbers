# C3 fourth pivots: original-source certificates

## A. Origin and provenance

These certificates address the original completed C3 source at cutoff `M = 80`,
with the C3/48 bracket, original Gamma completion, and original tail ledger.
The shifted sector `s = 1, n = 3` uses coefficient `c₈`; the central extension
certifies `s = 0, n = 3` using the same normalized coefficient boxes through
`a₈`. The source, completion, cutoff, camera, amplitude, and tail weights were
not modified.

- Worktree: `/home/thlinux/worktrees/c3-shifted-fourth-certificate-20261112`.
- Shifted certificate: PR #327, merged on 2026-11-13.
- Central extension: branch `agent/c3-central-fourth-same-boxes-20261113`,
  based on `bdbc1792e143dd8377cdb55638731aeea432b7db`, and not merged.
- Validation base: `6c5c97b03925c398bf77a561d6e76b14563265e0`; the branch tip before
  this resumed certificate work was `c5edad6`.
- Lean: 4.32.0; Mathlib pin
  `81a5d257c8e410db227a6665ed08f64fea08e997`; GreenFrame pin
  `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- Reused source and transport modules from `research/c3-cofactor-chiral-certification/`
  and `research/c3-cofactor-correlation-gate/`, including the M=80 head,
  `C3CompletionTail48`, Gamma crosswalk and error ledger, `SourceCoefficientGreen`,
  and the source/moment Schur identities.
- The odd third-order prefix determinant and positive-definite prefix are
  reused source-coefficient results. The fourth-direction sign is proved by
  the new source gate below; theta/Stieltjes positivity is not a premise.

## B. Results proved in Lean

The new and extended modules prove the following interfaces:

- `native_coefficient_candidate17_contains_c7` and
  `native_coefficient_candidate17_contains_c8`: source enclosures for the two
  highest coefficients needed by the 4×4 block.
- `normalized_native_coefficient17_contains`: for every `j : Fin 9`, the
  original native ratio `cⱼ/c₀` lies in its correlated rational candidate ball.
  The proof uses the M=80 head, the original Gamma residual and C3/48 tail,
  rounded grid endpoints, and the independent bound `c₀ > 49/100`.
- `native_normalized_fourth_cofactor_gate17`: the fixed-direction cofactor
  gate evaluated at the actual normalized native coefficients is positive.
- `native_normalized_fourth_determinant_eq_gate17` and
  `native_odd_fourth_bezout_determinant_positive17`: the cofactor gate is the
  determinant of the bordered normalized block, and the original shifted 4×4
  Bézout block has positive determinant.
- `native_odd_fourth_sourceSchur_positive17`: the shifted source Bézout Schur
  pivot at order 3 is positive, using the positive third-order prefix
  determinant and the exact bordered determinant factorization.
- `native_odd_fourth_momentSchur_positive17`:
  `0 < CarrySelfAdjointOperator.sourceMomentSchur nativeH 1 3`, transported
  through the existing identity `p_B = c₀² p_H` with the nonzero original
  completion coefficient.
- `native_odd_fourth_moment_posDef17`: using the original-source positive
  shifted 3×3 prefix and the newly certified shifted Schur pivot,
  `(sourceMomentMatrix nativeH 1 4).PosDef`.
- `native_normalized_even_fourth_cofactor_gate17` and
  `native_normalized_even_fourth_determinant_eq_gate17`: with the same
  normalized coefficient boxes through `a₈`, the original central-sector
  fourth cofactor gate equals the bordered determinant.
- `native_even_fourth_bezout_determinant_positive17` and
  `native_even_fourth_sourceSchur_positive17`: the original central 4×4
  source Bézout determinant and order-3 source Schur pivot are positive.
- `native_even_fourth_momentSchur_positive17` and
  `native_even_fourth_moment_posDef17`: the central native moment Schur pivot
  is positive, and `sourceMomentMatrix nativeH 0 4` is positive definite.

The central rational gate lower endpoint is exactly
`(1177581716 - 22122) / 10^50 > 0` (approximately `1.177559594 × 10⁻⁴¹`).
The central prefix uses source coefficient facts at orders 1 and 2 and the
already source-certified third pivot at order 2; the gate has no theta sign
dependency.

The interval proof is staged: candidate coefficient balls are first shown to
contain the native source; the odd-block components and the fixed-direction
energy/residual are then enclosed by rational balls; the final rational lower
endpoint is proved greater than `67/10^55`. The value is strictly positive.
The Python correlated preflight independently reports the sharper rational
lower endpoint
`6.74360518689508947997160988154063898922555 × 10⁻⁵⁴` for its exact interval
calculation. The Lean theorem relies on its own checked rational-ball
containment and endpoint proof, not on Python output.

The cofactor identity is algebraic and uses the adjugate form of the bordered
determinant. The inverse appears only in the later Schur factorization, after
the prefix determinant is known positive. The final moment-pivot statement
retains the factor `c₀²`; it does not identify this with any differently
normalized source remainder.

## C. Fourth-direction and determinant calculation

Let `aⱼ = cⱼ/c₀` be the normalized source coefficients. For a symmetric prefix
`A`, coupling vector `b`, lower-right entry `d`, and fixed direction `u`, the
formal gate proved in `FourthIntervalGate17.lean` is

```text
det(A) · (uᵀAu + 2bᵀu + d) − (Au+b)ᵀ adj(A) (Au+b).
```

By the exact bordered identity this equals the determinant of the block
obtained by evaluating the quadratic form at the direction `(u,1)`. The
rational boxes show that this value is positive for the actual native `a₀,…,a₈`.
Together with the source-certified positive prefix determinant, the bordered
determinant factorization yields the positive source Schur pivot. The existing
Schur transport then yields the native moment pivot `sourceMomentSchur
nativeH 1 3`.

This is a finite fourth-pivot certificate. It is not an all-order law and does
not by itself assert positive definiteness of every block in either tower.

## D. Original-source and interval transport

The certificate retains the source genealogy: original C3 brackets and M=80
head, completion through the original Gamma factor, coefficient extraction,
then the native Bézout/moment identities. It uses the exact formal-series
convolution, the normalized chart reciprocal recurrence through jet 16, the
correlated normalized completion boxes, and the original per-jet Gamma and
tail allowances. The head cache is checked against the rational `logBox` and
`expBox` evaluators, and Lean checks the integer-grid sample jets before their
use in the M=80 head sum.

For reproducibility, the order-14 and order-16 head enclosures are:

- order 14: `[1950031647244927799/10^30,
  1950031647244938748/10^30]`;
- order 16: `[590644054642505800/10^30,
  590644054642507801/10^30]`.

The normalized candidate balls through `a₈` use the same-log-π correlation.
Lean proves their native inclusions via the residual grid endpoints in
`FourthSourceGate17.lean`; `CoefficientBoxes17.lean` additionally proves the
direct source coefficient inclusions for `c₇,c₈` from the transported source
boxes. No independently widened coefficient box is used to close the sign.

## E. Finite C3 status

**GREEN for both original completed C3 fourth moment-Schur pivots certified
here.** The shifted pivot `sourceMomentSchur nativeH 1 3` is strictly positive
from its original M=80 source certificate. The central pivot
`sourceMomentSchur nativeH 0 3` is strictly positive from the same original
source coefficient boxes and the same M=80/C3-48/Gamma completion and tail.
Lean also proves `(sourceMomentMatrix nativeH 0 4).PosDef`. The central
source-side 4×4 Bézout determinant and its source Schur pivot are positive.
The new `native_odd_fourth_moment_posDef17` corollary also proves
`(sourceMomentMatrix nativeH 1 4).PosDef` from the source-certified shifted
3×3 prefix and fourth Schur pivot.

These results are specific to `s ∈ {0,1}, n = 3`. They do not certify later
pivots or all-order positivity. Positive definiteness is proved for both
4×4 moment matrices.

## F. Counterchecks and limitations

The script `preflight_source_boxes.py` also evaluates a much wider
per-coefficient enclosure. Its gate lower bound is about
`−2.177195073027048 × 10⁻⁴⁵`, so that enclosure alone cannot certify a sign.
This is a loss-of-correlation diagnostic, not a counterexample to the source
or to the correlated Lean certificate. The correlated normalized candidate
balls and their source inclusions are the inputs to the formal gate.

The positive prefix is a required dependency of the bordered Schur argument;
it is the previously source-certified third pivot. The fourth sign is not
inferred from alternating coefficient signs, small tail size alone, or a
positivity equivalence.

## G. Obligations still open

- The general all-order last-coefficient/determinant/Schur law and its TFVD
  head-tail transport are a separate task and are not proved by this finite
  C3 module.
- Both towers beyond the certified finite order remain open here.
- No general positive Gram representation, all-order Hankel positivity, or
  universal source inequality is established.

## H. Validation and audit

The updated `bash research/c3-shifted-fourth-certificate/validate.sh` passed
end to end in the configured worktree. It compiled every listed research
module with `-DwarningAsError=true`, regenerated the integer-grid and
amplitude tables, compiled `Audit17.lean`, ran both rational preflights,
scanned for `sorry`, `admit`, `native_decide`, and new axioms, and passed
`git diff --check`. The audit roots for the new coefficient, gate, determinant
and Schur theorems report only `propext`, `Classical.choice`, and `Quot.sound`.

The root `lake build --wfail` passed (8,850 jobs), as did
`scripts/audit-foundation.sh`, `scripts/audit-geometry.sh`, and
`scripts/audit-analysis.sh`. The first attempt to build this worktree's Mathlib
cache ran out of filesystem space. Validation then reused a complete sibling
cache after confirming the identical Lake manifest, Mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`, and Lean toolchain. The root build
and all three audit scripts were rerun successfully from this branch.

After adding the shifted 4×4 `PosDef` corollary, the modified
`FourthIntervalGate17.lean` and `Audit17.lean` were directly recompiled with
`-DwarningAsError=true`; the source-orientation audit passed for five roots,
closure 66,472, standard axioms only, and the specified theta dependencies
absent. The unchanged research modules, source-table regeneration, preflights,
and placeholder scan passed in the immediately preceding full `validate.sh`
run.

The correlated Python preflight reports the positive lower bound above. The
wide independent-box preflight reports the negative diagnostic bound above.
The legacy dependencies are imported from their recorded worktrees; the
task-specific validator compiles the research modules directly because the
root Lake build does not enumerate them automatically. Validation artifacts
are the modules and scripts named above; no external numeric result is used
as a Lean proof premise. PR #327 was opened against `main`; at the recorded
pre-merge check GitHub reported `CLEAN`/`MERGEABLE` and no status checks. It
was merged on 2026-11-13; merge commit:
`131079fb7539dea352945c9758fec86bad3e9591`.

The central-source extension is on branch
`agent/c3-central-fourth-same-boxes-20261113`, based on current `main` SHA
`bdbc1792e143dd8377cdb55638731aeea432b7db`; it is open as PR #329 and remains
unmerged. Its proof commit is `11615e06344dd610c8cc4747bbc656d6dd0c0ef5`.
The earlier shifted result remains PR #327, merge commit
`131079fb7539dea352945c9758fec86bad3e9591`.

## I. Next minimal obligation

Certify the central fifth source Schur pivot (`s = 0, n = 4`) from the
original C3 source with a separately audited gate; do not infer its sign from
the now-positive 4×4 central prefix.
