# Checkpoint — C3 shifted fourth pivot

- Status: GREEN for the finite original-source shifted pivot `sourceMomentSchur nativeH 1 3`; all-order positivity and the ordinary fourth pivot remain open.
- Branch: `agent/c3-shifted-fourth-certificate-20261112`; validated base `6c5c97b`; previous branch tip `c5edad6`.
- Source: original completed C3, M=80 head, C3/48 bracket, original Gamma completion and tail ledger; no source scales or weights changed.
- Pins: Lean 4.32.0, Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, GreenFrame `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa`.
- New modules: `TightNormalizedChart17.lean`, `FourthSourceGate17.lean`, `FourthIntervalGate17.lean`; earlier coefficient/grid modules were extended; `validate.sh` and `Audit17.lean` include them.
- Proved: native normalized coefficient containment through `a₈`; fixed-direction cofactor gate lower bound `> 67/10^55`; shifted 4×4 source Bézout determinant positive; shifted source Schur pivot positive; native moment pivot `0 < sourceMomentSchur nativeH 1 3`.
- Dependencies: positive odd third-order source prefix, original coefficient/head/Gamma/tail enclosures, exact bordered determinant identity and existing source-to-moment Schur scaling `p_B = c₀² p_H`.
- Sign provenance: the fourth-direction sign comes from the original-source correlated interval gate. No theta/Stieltjes positivity is used as its sign premise.
- Correlated Python preflight: exact gate lower `6.743605186895089… × 10⁻⁵⁴`; Lean proves source inclusion and its own coarser strict lower bound.
- Negative control: independently widened coefficient intervals give about `−2.177195073027048 × 10⁻⁴⁵`; this loses correlation and does not contradict the formal correlated gate.
- Full `bash research/c3-shifted-fourth-certificate/validate.sh` passed after the final report/diagnostic wording update: all Lean modules compiled with warnings as errors; both table generators, the axioms audit, both preflights, placeholder scan, and `git diff --check` passed.
- Axioms of new public roots: only `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `admit`, `native_decide`, or new axiom declarations.
- Updated report: `REPORT.md`, including finite GREEN scope and remaining obligations; diagnostic scripts now distinguish the loose negative control from the correlated Lean gate.
- PR: #327, `https://github.com/thiagomassensini/geometry-of-numbers/pull/327`, against `main`; GitHub reports `CLEAN`/`MERGEABLE` and no status checks are configured or reported.
- Commit: `f4c5a14970af6f89e7a108be3f162d165dbc6ba6` (`research(c3): certify shifted fourth source pivot`), pushed to the task branch.
- Next exact step: perform the ordinary protected merge of PR #327; if GitHub rejects it for protection or missing review/check requirements, leave it open and record the block.
