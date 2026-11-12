# Checkpoint — C3 cofactor / third odd pivot

MISSION: certify the third odd pivot from the completed C3 source, then transport to the chiral order-11 balance.
BASE_SHA: `e4f5de51cad523963a327c8295067f88fc7855fa` (`origin/main` after PR #321).
BRANCH: `agent/c3-cofactor-chiral-certification-20261112-next`.
HEAD_SHA: `1b1b05a` (directional cofactor and order-11 transport; pushed).
PHASE: General cofactor identities complete; order-11 chiral transport now uses the independently certified C3 odd prefix.
STATUS: PARTIAL; no positivity certificate for either third-direction margin is claimed.
FILES ADDED: `GeneralCofactorIdentity.lean`, `ChiralOrder11.lean`; validator and report updated.
THEOREMS: `border_det` for arbitrary finite prefix, including singular and empty prefixes; `border_directional_identity` for every direction with symmetric prefix; explicit identification `vᵀBv=directionalEnergy`; cofactor-vector identities and 3×3 regressions; completed-C3 odd-prefix invertibility; order-11 balance and scaled-relative-deficit limit.
HYPOTHESES: commutative ring only for determinant/vector identities; no invertibility, recurrence, source, or positivity hypotheses.
VALIDATION: research validator passed all 20 modules with warnings as errors; `research/c3-odd-head-source/validate.sh` passed eight modules; `lake build --wfail` passed (8,850 jobs); all three root audits passed. Axiom output for new theorems is only `propext`, `Classical.choice`, `Quot.sound`.
LAST COMMIT: `1b1b05a feat(c3): add directional cofactor and odd order-11 transport` (pushed to origin).
PRIOR EVIDENCE: base already passed 19-module research validation, `lake build --wfail` (8,850 jobs), and three root audits.
OPEN SOURCE OBLIGATION: the exact M=48 rational interval for the odd cofactor margin still contains zero, approximately `[-9.1071e-32,1.0049e-31]`. No GREEN claim.
NEXT EXACT ACTION: finalize this report/checkpoint, push the documentation update, and open the PARTIAL PR with the source margin stated as open.
BLOCKER: none; current interval width is the known mathematical obstacle.

Integrated history: PR #318 `21c24415de48b184f5ad0498f9ac28e7c64a8195`; #319 `d4df30eb426653121c42cfe1bcfed68d3ce9bfed`; #320 `f5b403f31cc63a1f1a4af069180b0516f88841f1`; #321 `e4f5de51cad523963a327c8295067f88fc7855fa`.
Pins unchanged: Lean 4.32.0, mathlib `81a5d257`, GreenFrame `cd2d838`. Original working tree with pre-existing changes remains untouched.
