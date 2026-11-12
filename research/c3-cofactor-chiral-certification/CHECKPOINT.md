# Checkpoint — C3 cofactor / third odd pivot

- Base: `origin/main` `1e0a6c80957fb7a1385cdb6a1869d04dbf40b64d`; branch `agent/c3-cofactor-chiral-certification-20261112`.
- Worktree: `/home/thlinux/worktrees/c3-cofactor-chiral-certification-20261112`; pins unchanged (Lean 4.32.0, mathlib `81a5d257`, GreenFrame `cd2d838`).
- PRs #316/#317 confirmed integrated; original dirty worktree preserved.
- Latest code commit: `e4aa282` (pushed pending).
- Phase: exact C3/48 head/tail, completed tail bound, and rational head jet boxes through order 12.
- New modules: `CofactorIdentity`, `SchurGate`, `C3Regression`, `IntervalGate`, `SourceGate`, `C3Acceleration48`, `C3Power26Step`, `C3Power26Tail`, `C3Power26Series`, `C3Boundary48Finite`, `C3Boundary48Infinity`, `C3Boundary48Stencil`, `C3CompletionTail48`, `C3Head48Jet`, `C3Head48Boxes`.
- Cofactor identity: exact 3×3 determinant/cofactor formula, including singular prefixes; positive-definite gate is explicitly conditional on `a>0`, prefix determinant `D>0`, and strict cofactor margin.
- Canaries: positive conditional case; failing negative margin; singular-prefix identity; noncritical direction; reused synthetic negative control. No arbitrary-source positivity claim.
- Interval gate: rational candidate boxes imply positive odd block margin and PosDef, but source inclusion in those boxes is unproved.
- C3/48: exact doubled cell identity, finite window with both boundaries, boundary tends to zero, exact infinite decomposition into the original `realCpBracketCutoffTail` plus the order-26 lattice series, and exact 24-point stencil.
- Completion: `completed_native_head_tail48` is an exact split using the original value multiplier and Gamma; `completed_tail48_jet_error_through_twelve` proves its tail contribution is at most `10⁻²⁰` for all orders 0…12 by the original multiplier bound and Cauchy.
- Head: `accelerated_head48_jet_formula` identifies all 13 factorial-normalized jets with the exact finite material samples; rational interval propagation proves `head48_reference_contains` for every order 0…12, using sample addresses only through 169.
- Order-26 series: summability, complex norm bound, and `M=48`, `k≤6` pre-Cauchy budget `≤10⁻²⁰`; this is not yet a completed-characteristic tail bound.
- Validation: all 15 task modules compiled directly with `-DwarningAsError=true`; new head formula and interval theorems use only `propext`, `Classical.choice`, `Quot.sound`.
- Recent validation fix: `C3Regression` now imports the actual existing synthetic negative-control theorem name `negative_control_not_posSemidef`.
- Open: extend Gamma jet enclosures through order 12; combine all original completion factors and the head/tail ledger into completed source boxes through `c₆`; unconditional cofactor margin; independent chiral-order-11 transport.
- Next exact step: derive rational Gamma jet boxes through order 12 from the existing finite Gamma formula and `native_gamma_jet_error`, then propagate them with the verified head intervals.
