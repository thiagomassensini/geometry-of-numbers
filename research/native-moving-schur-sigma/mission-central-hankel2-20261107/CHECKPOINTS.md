# Checkpoints

## Checkpoint 0 — inventory and isolation

- [x] Read the full mission objective and `AUDITORIA_POSITIVIDADE_CENTRAL_C2_2026-11-07.md`.
- [x] Fetch `origin`; record `origin/main = eb00da2374a2a0a5f563ab94925a96c2bb7a019a`.
- [x] Create branch `agent/c2-central-hankel2-allorder-20261107` and isolated worktree `/home/thlinux/worktrees/geometry-of-numbers-c2-central-hankel2-allorder-20261107` from `origin/main`.
- [x] Pin is Lean 4.32 (`leanprover/lean4:v4.32.0`). Reserve mission-specific `SIGMA_OUTPUT_DIR`; no C5 outputs/caches reused.
- [x] Inspect current Geometry worktrees and open PRs. Geometry has no open PR at inventory; Momentos PR #2 is open at `49c9e53946708e3ac1690c25fe096a723ab7bf7d`.
- [x] Identify active C5 build in a separate worktree and defer Lean builds until it exits.
- [x] Read actual declarations for original `sigmaPadeD`, count, boxes, zero location/order, native continuation, and C4 jet normalization; see `THEOREM_MAP.md` and `SESSION_STATE.md`.
- [x] Read the Momentos PR #2 all-window caderno and Lehman contour note from their audited head and record exact paths/hashes as reference data; the exact arithmetic checker hash is also recorded in `SESSION_STATE.md`.
- [x] Trace the import path to the original completed jet and identify `sigma_log_jet_center_eq_canonical` as an existing source-to-canonical correspondence.
- [x] Verify existing `SigmaHeight50Integration` Lean 4.32 evidence against current source hashes. The prior build log SHA256 is `8f1c18253d9db4e5ea562fccbb569adf565ce5fe243b3c028d2f7f1d4cc2b606`; the integration and exported height-50 certificates list only `propext`, `Classical.choice`, and `Quot.sound`.

Checkpoint 0 is complete. The worktree fast-forwarded to `ebd6c57c33edcf8596f09889c7bf956e7d9b284f` after the C5 prefix96 merge, then waited until the clean C5 reproduction exited before starting B1 builds. All B1 outputs use the mission-only output root, and no C5 cache was used.

## Checkpoint 1 — B1 algebra and rational gate

- [x] Prove the generic finite power-sum identity, Vandermonde-pair formula, five-term determinant expansion, and signed absolute error bound in `SigmaCentralTenModeAlgebra.lean`.
- [x] Prove exact rational box bounds, four refined low-index margins, and the global tail ratio for `s ≥ 4` in `SigmaCentralTenModeRationalGate.lean`.
- [x] Replay the Momentos exact `Fraction` checker and independently reproduce the D0 failure under the coarse-only tail bound.
- [x] Prove a conditional theorem for every original central consecutive 2×2 minor, retaining the original `completedSigmaLogJet` and `sigmaPadeD`, with decomposition, box, global-tail, low-index-sign, and refined-tail premises explicit.
- [x] Compile all four modules with warnings as errors, pass the fail-closed axiom audit, record source/output hashes, and preserve the exact rational replay.
- [ ] Commit and open a small PR for this compiled B1 checkpoint.

## Checkpoint 2 — height-50 ten-zero family

- [ ] Build one family of ten positive heights with open rational boxes, simple continuation zeros, multiplicity accounting, and no other positive-height zeros ≤50.
- [ ] Preserve the zeta-to-original-native identification and prove the exact center is nonzero.
- [ ] Verify the normalization from original C4 jets to the characteristic log derivative.
- [ ] Do not infer the infinite product or tail from the finite count.

## Checkpoint 3 — analytic bridge and tails

- [ ] Formalize the order ≤1 normalized Hadamard product and its log derivative, or document precise named hypotheses and prove all consequences conditionally.
- [ ] Formalize Lehman with quantitative constants or derive a Lean-certified alternative with sufficient margins.
- [ ] Prove the global tail, low-index nonnegative real parts, and refined `T_n` inequalities.
- [ ] Keep all analytic assumptions visible; add no new axioms.

## Checkpoint 4 — original theorem

- [ ] Compose the ten-mode data and tail into `∀ s, 0 < CarrySigmaPade.sigmaPadeD 0 s`.
- [ ] Audit the full theorem closure (`#print axioms`, no new axioms/sorry/admit), builds, hashes, oleans, command line, and remote PR state.
- [ ] State the scope as 2×2 central minors only.

## Checkpoint 5 — optional future extension

Not started. Do not enter the radius-600/displacement-law route before the central mission closes or the user explicitly redirects the task.
