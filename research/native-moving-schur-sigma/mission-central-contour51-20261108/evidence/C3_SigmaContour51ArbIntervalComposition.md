# C3 Arb interval composition bridge

## Result

`SigmaContour51ArbIntervalComposition.lean` proves sound composition from explicit rational
rectangles for the source variables and analytic factors to a rectangle for the original response
and residual integrands. The core theorems are:

- `contour51ArbSigmaXiLogDerivativeBox_contains`
- `contour51ArbOriginalResponseBox_contains_lower_path`
- `contour51ArbN0ResidualIntegrandBox_contains`
- `contour51ArbResidualIntegrandBox_contains`
- `contour51Arb4096N0ArcEvaluatorInclusion_of_component_boxes`
- `contour51Arb4096N0AllArcEvaluatorInclusion_of_component_boxes`

The arithmetic uses `ComplexInterval.divBox` and `contains_divBox` from
`SigmaContour51ComplexIntervalDivision.lean`. The calls for `1/s`, `1/(s-1)`, `ζ'/ζ`, and the
final division by the powered contour parameter each carry an explicit proof that the lower endpoint of
the corresponding squared-norm interval is positive. `normSqRange` supplies the squared-norm
enclosure, and `contains_normSqRange` transports its containment.

The source response on the lower semicircle is rewritten with
`contour51OriginalResponse_eq_arb_formula_lower_path`. The component hypotheses retain boxes for
`s`, `ζ(s)`, `ζ'(s)`, `digamma(s/2)`, `log π`, and the contour parameter. The arc structure also
requires rational comparisons between the real part of the composed rectangle and the exported
4096-arc endpoints. From these fields, Lean proves pointwise inclusion on every point of the full
closed arc. The all-arcs theorem gives exactly the `n = 0` first conjunct of
`contour51Arb4096FirstThreeArcEvaluatorInclusion` after unfolding that definition.

The generic theorem `contour51ArbResidualIntegrandBox_contains` handles any `n`: it encloses the
denominator by `parameterBox.powI (2*n+1)`. Positivity of the norm-square enclosure of that powered
box remains an explicit hypothesis. This is a generic composition lemma, not an `n=1` or `n=2`
arc certificate; the all-arcs adapter currently covers only `n=0`.

## Open inputs and scope

This module does not construct or prove any component rectangle, denominator positivity proof, or
endpoint comparison. Those remain hypotheses of `Contour51Arb4096N0ArcComponentBoxes`. In
particular, it does not claim the Arb endpoint tables include the Lean evaluator: endpoint
arithmetic alone cannot fill the component-containment fields. The `n = 0` result by itself does
not close `contour51Arb4096FirstThreeArcEvaluatorInclusion`: component boxes and endpoint
comparisons for `n = 1` and `n = 2` are still required. The module does not prove an integral bound
or central positivity.

## Compile and axiom audit

Compiled with Lean 4.32.0 via `compile_sigma_pade.sh SigmaContour51ArbIntervalComposition`,
`-DwarningAsError=true`, and the exclusive output directory
`/home/thlinux/tmp/c2-contour51-20261108-lean432`. The compilation used the existing B1/B2,
Carry, Mathlib, and C2 integration/external OLean roots read-only. The checked-in output log is
`C3_SigmaContour51ArbIntervalComposition-success.log`; the successful OLean is at
`/home/thlinux/tmp/c2-contour51-20261108-lean432/SigmaContour51ArbIntervalComposition.olean`.
All seven new theorem audits report only `[propext, Classical.choice, Quot.sound]`. The source
contains no `sorry`, `admit`, or new axioms.

The diagnostic build history is preserved alongside the successful log. Attempts 1 and 2 exposed
type and goal-shape errors during the first composition proof (Lean's recovery diagnostics printed
`sorryAx` for declarations that failed to elaborate; those outputs are not successful artifacts
and the final source contains no such dependency). Attempt 3 was rejected by `warningAsError` for
unnecessary tactic sequencing. Attempt 4 was rejected by `warningAsError` because `sub_eq_add_neg`
was an unused simp argument. Attempt 5 compiled the n=0 composition. Attempt 6 compiled the added
generic `powI (2*n+1)` quotient theorem; its output is the successful log above.

SHA-256 for diagnostic logs:

- Attempt 1 failed: `dd03fcebfb641dae50b7f5cd950b9dfd57da2ce1caea1b2af369544f3ffd3759`
- Attempt 2 failed: `e665542e6040e89e941f86688324109628d288dfb6c6452b2ca3142c228ab5e5`
- Attempt 3 failed: `cb625581122ef5cded7f0ed0c86c2f73436981c4beb8e77039deac962b992b00`
- Attempt 4 failed: `77f294dc1d295c3d1c900ac67c3475d2f1cb926f8cee6842e63bab3c76ca4036`
- Attempt 5 intermediate success: `923fd6b49816a853b3c053eb013ee864420d41e75246ad24eb1f45eb699b4eac`

SHA-256:

- Lean source: `bbe5faf135e424940267e1e2b50083c1e6c38149de971aed520dc0bb0758cf0c`
- Division helper source: `d10933c086f71ddfe48ad9b6fdd1ef5f3bf4ae95fe5cd6a072cb914195a4d0c9`
- OLean: `1eb90fb78f205fc79d3e4caa18283ae317ecd0836e1e79f1745e8a7e1b1819a5`
- Build log: `35855d1d40f83e51c651821f5808015da0ab187701cd0b5eb87b16a2287c5e37`
