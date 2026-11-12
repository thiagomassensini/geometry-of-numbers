# Checkpoint — C3 cofactor / third odd pivot

MISSION: certify the third odd pivot from the completed C3 source, then transport to the chiral order-11 balance.
BASE_SHA: `e4f5de51cad523963a327c8295067f88fc7855fa` (`origin/main` after PR #321).
BRANCH: `agent/c3-cofactor-chiral-certification-20261112-next`.
HEAD_SHA: `75807f8` (general singular cofactor identity).
PHASE: Checkpoint 0 complete; general-dimensional algebraic cofactor identity is proved locally.
STATUS: PARTIAL; no positivity certificate for either third-direction margin is claimed.
FILES ADDED: `GeneralCofactorIdentity.lean`; validator and report updated.
THEOREMS: `border_det` for arbitrary finite prefix, including singular and empty prefixes; `border_mulVec_cofactor`; `cofactorVector_quadratic`; 3×3 determinant and cofactor-vector regressions.
HYPOTHESES: commutative ring only for determinant/vector identities; no invertibility, recurrence, source, or positivity hypotheses.
VALIDATION: direct Lean compile with warnings as errors passed; public theorem axioms are the standard `propext`, `Classical.choice`, `Quot.sound` set. Full research validator is running.
LAST COMMIT: `75807f8 feat(c3): prove general singular cofactor identity` (pushed to origin).
PRIOR EVIDENCE: base already passed 19-module research validation, `lake build --wfail` (8,850 jobs), and three root audits.
OPEN SOURCE OBLIGATION: independent/correlated native C3 coefficient bounds still give a third odd cofactor-margin interval containing zero; no GREEN claim.
NEXT EXACT ACTION: derive a correlation-preserving rational enclosure for the native odd cofactor margin from the existing C3 coefficient formulas and compare it with the strict zero threshold.
BLOCKER: none; current interval width is the known mathematical obstacle.

Integrated history: PR #318 `21c24415de48b184f5ad0498f9ac28e7c64a8195`; #319 `d4df30eb426653121c42cfe1bcfed68d3ce9bfed`; #320 `f5b403f31cc63a1f1a4af069180b0516f88841f1`; #321 `e4f5de51cad523963a327c8295067f88fc7855fa`.
Pins unchanged: Lean 4.32.0, mathlib `81a5d257`, GreenFrame `cd2d838`. Original working tree with pre-existing changes remains untouched.
