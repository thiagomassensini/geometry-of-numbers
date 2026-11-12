# Checkpoint — C3 cofactor / third odd pivot

- Base: `origin/main` `1e0a6c80957fb7a1385cdb6a1869d04dbf40b64d`; branch `agent/c3-cofactor-chiral-certification-20261112`.
- Worktree: `/home/thlinux/worktrees/c3-cofactor-chiral-certification-20261112`; pins unchanged (Lean 4.32.0, mathlib `81a5d257`, GreenFrame `cd2d838`).
- PRs #316/#317 confirmed integrated; original dirty worktree preserved.
- Latest code commit: `f03d4ad` (pushed pending).
- Phase: exact C3/48 infinite boundary decomposition proved for the original uncompleted bracket.
- New modules: `CofactorIdentity`, `SchurGate`, `C3Regression`, `IntervalGate`, `SourceGate`, `C3Acceleration48`, `C3Power26Step`, `C3Power26Tail`, `C3Power26Series`, `C3Boundary48Finite`, `C3Boundary48Infinity`.
- Cofactor identity: exact 3×3 determinant/cofactor formula, including singular prefixes; positive-definite gate is explicitly conditional on `a>0`, prefix determinant `D>0`, and strict cofactor margin.
- Canaries: positive conditional case; failing negative margin; singular-prefix identity; noncritical direction; reused synthetic negative control. No arbitrary-source positivity claim.
- Interval gate: rational candidate boxes imply positive odd block margin and PosDef, but source inclusion in those boxes is unproved.
- C3/48: exact doubled cell identity, finite window with both boundaries, boundary tends to zero, and exact infinite decomposition into the original `realCpBracketCutoffTail` plus the order-26 lattice series.
- Order-26 series: summability, complex norm bound, and `M=48`, `k≤6` pre-Cauchy budget `≤10⁻²⁰`; this is not yet a completed-characteristic tail bound.
- Validation: all 11 task modules compiled directly with `-DwarningAsError=true`; public theorem axiom output only `propext`, `Classical.choice`, `Quot.sound`.
- Recent validation fix: `C3Regression` now imports the actual existing synthetic negative-control theorem name `negative_control_not_posSemidef`.
- Open: 24-address stencil equality; completion/Cauchy transport; completed source coefficient boxes through `c₆`; unconditional cofactor margin; independent chiral-order-11 transport.
- Next exact step: prove `c3Boundary48` equals the 24 rational-weighted samples from addresses `a,…,a+23`, checking the supplied weights by Lean.
