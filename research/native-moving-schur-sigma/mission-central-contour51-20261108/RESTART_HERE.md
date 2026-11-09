# Restart point — radius-51 contour route

## Current state

- Read the full PR #306 investigation, copied it into this branch, and reproduced its Python probe. The grid and floating-point jet values remain experimental evidence only.
- Worktree: `/home/thlinux/worktrees/geometry-of-numbers-c2-contour51-20261108`.
- Branch: `agent/c2-contour51-20261108`.
- Base: B2 PR #311 head `7509f5d9404fe2514d4c609acb4ad10b9b02ab54`; B1 is inherited through B2.
- Exclusive Lean output: `/home/thlinux/tmp/c2-contour51-20261108-lean432`.
- PR #304, #311, and #306 are open and mergeable; their heads were checked after `git fetch origin`. Do not modify their branches.
- C0 is committed and pushed as `96314ff` (`Docs: isolate radius-51 contour C0`).
- C1: `SigmaContour51DiskBridge.lean` packages the height-52 multiplicity exhaustion and exact radius-51 root classification. It compiled on Lean 4.32.0 with warnings-as-errors; both theorem axiom reports are `[propext, Classical.choice, Quot.sound]`. Commit `4b104771b7cc3dfbd487584b57b5bba1680e273e` is pushed. The source, successful build log, and hashes are recorded in `VALIDATION.md`.
- C2: `SigmaContour51Residue.lean` and `SigmaContour51FiniteContour.lean` compile on Lean 4.32.0 with warnings-as-errors. The newer `exists_contour51_corrected_log_derivative` constructs the finite analytic correction across simple roots; `exists_completedNative_contour51_corrected_log_derivative` fixes one exact C1 root list, exposes its ten rational height boxes, and proves the correction for every `n`; `completedNative_contour51_jet_residue_identity` proves `normalized ∮ R(z)/z^(2*n+2) = completedSigmaLogJet 0 n - ∑ i, (ts i)^(-2*n-2)` for that same root list and every `n`. Each relevant `#print axioms` reports `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or new axiom. The successful final build is attempt 34; the source/OLean/log hashes are recorded in `VALIDATION.md`.
- C4/C6: `SigmaContour51RationalGate.lean` compiles on Lean 4.32.0 with warnings-as-errors. Its conditional radius-51 tail, four exact-rational shallow margins, B1 large-window implication, and wrapper for original `sigmaPadeD` have axiom reports `[propext, Classical.choice, Quot.sound]`. C2 supplies one fixed root list and its rational height boxes. The source wrapper derives `hdecomp` and `hbox` from C2. The all-window premises still to supply in Lean are the circle bound and all six residual interval transfers.
- `SigmaContour51SourceTail.lean` now performs that composition: it proves the reciprocal-square box bounds and original-jet decomposition from the fixed C2 roots, transports the C2 contour identity through C4's `C=40` bound, and feeds it into C6. `completedNative_sigmaPadeD_pos_of_contour51_bound` concludes the all-window theorem conditional only on `‖R‖≤4/5` and the six central residual signs. `completedNative_sigmaPadeD_zero_pos_of_contour51_bound` isolates `s=0` under only `e_0,e_2≥0` plus the circle bound; it does not assume the sign of `e_1`. Lean 4.32 build attempt 10 succeeds with only standard axioms; hashes are in `VALIDATION.md`.
- C3 is supported by `certify_contour51_bound.py`: 512 Arb interval arcs and explicit Cauchy Taylor remainders prove `|R|<4/5` on the full radius-51 circle. `certify_contour51_residuals.py` reuses the evaluator on 4096 arcs and produces exact rational intervals for `e_0,…,e_5`; strict positive lower margins are recorded in `C3_ARb_CERTIFICATE.md` and `evidence/C3_ARb_RESIDUALS_4096.json`. Both are rigorous external Arb certificates, not yet Lean theorems.
- `SigmaContour51ArbContourBridge.lean` compiles the path identity, source evaluator bridge, and conditional integration of all six residual orders. `contour51OriginalResponse_eq_arb_formula_lower_path` proves the explicit zeta/Gamma/digamma expression throughout `u∈[0,1]`; C1 and the path geometry discharge `F(z)≠0`, `0<Re(s)`, and `s≠1`, while zeta nonvanishing follows from exact factorization. The remaining gap is the universal pointwise inclusion of the Lean evaluator in each complete-arc Arb range, including Taylor/Cauchy remainders.
- Draft PR #314 is open and stacked on B2 PR #311 (`agent/c2-central-ten-heights-b2-20261108`). Earlier commits publish the C2 source identity and conditional C2→C4→C6 composition; this incremental checkpoint adds the Arb residual certificate and its conditional Lean gates. Keep #314 open and in draft while the Arb-to-Lean obligations remain.
- C5 continues in its separate worktree/cache under the user's parallel-build authorization. Do not use or modify its worktree/cache. Keep modules in this branch sequential and use only its exclusive output root.
- `SigmaContour51BoxSensitivity.lean` now proves six exact rational upper budgets for the current ten-mode box widths and the sufficient original-jet lower-margin interface for `e_n≥0`. It formalizes C5's `d=0` source map: its product is the square of `completedNativeOperatorCharacteristic`, and on the proved genuine strip it equals the square of `completedNativeCharacteristicContinuation`; the source-log derivative has coefficients `2H_n`, and `e_n` equals half that source moment minus `P_n`. The strip condition is explicit, and none of the nonzero-displacement C5 boxes has been transported.

## Next action

The next minimal step toward an unconditional first-window result is to prove `contour51Arb4096FirstThreeArcEvaluatorInclusion` for every point of every closed arc, including the validated Taylor/Cauchy remainder. The six exact rational tables, all twelve weighted sums, and the conditional list-to-integral transfers for `n=0,…,5` now compile; the first-window determinant then gives `1/1000000000 < sigmaPadeD 0 0` from the first three integral intervals without global `hR`. The all-window target still needs universal inclusion for all six orders and the separate Lean transfer of the 512-arc bound `‖R‖≤4/5`. The algebraic C5 `d=0` specialization is proved, but no displaced interval has been moved to the center; do not treat shifted `d=0.0495` or `d=0.1` conditional determinant boxes as center residual signs. C5's worktree/cache remain isolated, and its Bernoulli table and zeta/Gamma nodes were not rebuilt. C1's multiplicity argument uses `RHHeight.mem_and_simple_of_Ncount_le`, ten distinct B2 witnesses, and `RHHeight.ncount_three_fiftytwo`; `sigmaContinuation_zero_re_ne_zero_of_height50` excludes zero ordinates, `RHHeight.low_height` excludes `0 < Im ρ ≤ 3`, and evenness reflects negative roots.

## C2 update — 2026-11-08

- **Proved:** the global finite gluing, radius-51 boundary relation, Cauchy reduction, original-source Taylor coefficient, and exact signed-root pairing. No Hadamard factorization or zero-defined moments enter.
- **C3 status:** Arb/Acb certifies `|R| < 0.746413 < 4/5` on all 512 arcs. It is not yet a Lean theorem. Until that bridge is proved, C4's `C=40` tail remains conditional.
- **Six central residuals:** the external Arb intervals give strict rational lower margins `9/1000`, `9/10000000`, `9/50000000000`, `1/25000000000000`, `1/100000000000000000`, and `1/500000000000000000000`. Lean checks all six exported endpoint comparisons, exact weighted arc sums, and the conditional transfer to all six path integrals. The pointwise Arb-to-Lean inclusion remains open, so these margins are not yet Lean signs for `e_n`. The old mpmath values remain probes only.
- **Exact determinant margins already proved:** C6 proves positive rational lower bounds for its four shallow-window gates. Their decimal displays are approximately `1.233805751396619e-10`, `2.370461448625535e-15`, `1.677704301041960e-20`, and `4.956177598481227e-26` for `s=0,1,2,3`. These are determinant margins conditional on the residual sign/tail/source-box assumptions; they are not margins for the six `e_n` signs.
- **Remaining hypotheses:** for all windows, prove the circle bound in Lean and the six Arb interval transfers. For the direct first-window gate, only the interval transfers for `e_0,e_1,e_2` are needed; that gate handles the five determinant terms with a strict rational margin. No unconditional result is claimed while the interval-transfer bridge is open.
- **Smallest first-window target:** prove the pointwise proposition `contour51Arb4096FirstThreeArcEvaluatorInclusion` on all closed arcs, including the validated Taylor/Cauchy remainder. The compiled conditional adapter then supplies `contour51ArbFirstThreeLowerPathResidualIntervalBounds`; the rational determinant gate produces `1/1000000000 < sigmaPadeD 0 0`.
- **C5 reuse boundary:** the reusable parts include rational interval arithmetic, C2 source normalization/transport, and `c5_pi_log_interval_contains`. `SigmaContour51C5PiBridge.lean` now turns that real interval into a box for the exact complex `log π`. C5 zeta certificates are isolated rational nodes near `1/2+0i`, without ζ′ or Taylor boxes; fixed Gamma nodes do not enclose digamma on the contour. Displaced determinant signs at `d=99/2000` and `d=1/10` do not enclose central residuals `e_n`. Do not rerun its Bernoulli table or full zeta/Gamma node list; any node transport or center specialization needs an explicit quantitative theorem.

## C2 update — exact width sensitivity and center transport

- `SigmaContour51BoxSensitivity.lean` compiles with warnings as errors. It proves current power-sum widths below rational budgets `14/10^6`, `9/10^8`, `6/10^10`, `4/10^12`, `3/10^14`, and `2/10^16` for `n=0,…,5`, and gives a sufficient source-jet margin theorem. These budgets are not lower margins for `e_n`.
- The old mpmath probe comparison suggests no narrowing for the first two indices, then potential refinement of the first 1, 3, 4, and 5 height intervals for `n=2,3,4,5`. This is only a prioritization hint until rigorous `H_n` interval bounds are obtained.
- The C5 center transformation is now a Lean theorem: at `d=0`, the original displaced product is `completedNativeOperatorCharacteristic²`, identified with `completedNativeCharacteristicContinuation²` on the genuine strip; C5's source log-derivative coefficient equals `2H_n`; and the residual is half that source moment minus the same ten-mode power sum. The nonzero-displacement C5 numerical boxes still require quantitative transport or direct center evaluation.
- All new theorem axiom reports are `[propext, Classical.choice, Quot.sound]`; the generic C5 source audit checks 57,386 dependencies and preserves the original source. Evidence and hashes are in `VALIDATION.md`.
- Still open, exactly: (1) the universal per-arc evaluator inclusions for `n=0,…,5`, including Taylor/Cauchy remainder bounds; (2) a Lean derivation of `‖R‖≤4/5` on `|z|=51`. The first-window determinant uses only indices `0,1,2`; all windows need all six plus the global circle bound. No unconditional positivity is claimed.

Before every Lean build, check for active Lean/Lake processes; only the new output root may be written. Use the existing upstream C2 integration/height-52, B1, and B2 OLean artifacts read-only. Do not rebuild those upstream modules or the C3 module, and do not use C5 caches; new contour modules in this branch may be compiled sequentially.

## Source boundary

Keep `completedNativeCharacteristicContinuation` as the original continuation. It is the existing `completedRiemannZeta₀` expression under `operatorHeightParameter`; `completedNativeCharacteristicContinuation_eq_native` identifies its original native germ on the established strip. Never define `F`, `R`, or `H_n` from the zeros.

The unconditional all-order positivity target is not established by C0 or C1. B1's `hdecomp`, `he`, `hnonneg`, and `htail` remain explicit until the later checkpoints actually prove replacements.

## Latest C3 contour bridge increment

`SigmaContour51ArbContourBridge.lean` now contains the compiled theorem
`contour51OriginalResponse_circle_norm_bound_of_lower_semicircle_uniform_bound`: a uniform
`4/5` bound on the exact lower semicircle implies the required full-circle `hR`, by periodicity
and oddness of the original response. The input proposition is
`contour51ArbLowerSemicircleUniformResponseBound`; it is still open from Arb data because Lean
does not yet prove the evaluator inclusion and Taylor/Cauchy remainder bound on every one of the
512 arcs. The separate 4096-arc residual inclusion remains open for `n=0,…,5`; the minimum next
lemma for the first unconditional result is its restriction to `n=0,1,2`. Exact margins and the
new Lean build hash are recorded in `VALIDATION.md`. The existing source-response, C2 meromorphic
residue identity, all five determinant cross terms, and the distinction among the source residual,
the material C2 tail, and evaluator truncation remainder remain in force.

Latest module: `SigmaContour51ArbBoundCertificate512.lean`. It verifies every rational response
upper endpoint in the 512-arc table, proves the partition cover, and gives a conditional chain
from `contour51Arb512ResponseArcEvaluatorInclusion` to the full-circle `hR` and the existing
all-window theorem. The theorem still leaves six residual signs explicit. Proving the 512
pointwise inclusion, including Taylor/Cauchy remainders, is open; the separate 4096-arc residual
inclusions are also open, with `n=0,1,2` the first-window minimum. Logs and hashes are in
`VALIDATION.md`.

### Latest C3 formal Taylor step

`SigmaContour51TaylorRemainder.lean` compiles generic Cauchy bounds for the value and derivative
Taylor tails, including the exact weighted-geometric derivative remainder. It also proves that
rational complex interval boxes for exact Taylor coefficients and the displacement, inflated by a
proved rational remainder, contain the function or derivative value. These results still require
the coefficient boxes, `DiffContOnCl` plus a boundary majorant, and the closed-arc displacement
bound. They do not verify those inputs for zeta/digamma or connect the 512/4096 tables to the
original Lean evaluator. No residual signs or central positivity are discharged. See
`OPEN_OBLIGATIONS.md` for the exact remaining inputs and `VALIDATION.md` for the Lean 4.32 build,
axiom audit, and hashes.

### Latest C3 interval division step

`SigmaContour51ComplexIntervalDivision.lean` proves sound complex rectangular division when the
caller supplies a denominator norm-square interval with a strictly positive rational lower bound.
It also constructs a containing norm-square interval from a complex rectangle. This is reusable
for the `1/s`, `1/(s-1)`, `ζ′/ζ` and residual-integrand quotients in the original evaluator. The
component enclosures and positive lower bounds still need separate proofs; no Arb evaluator
inclusion or residual sign follows from this generic arithmetic lemma. See `OPEN_OBLIGATIONS.md`.

### Latest C3 response and residual composition

`SigmaContour51ArbIntervalComposition.lean` now composes explicit boxes for the source response
and its residual quotient. The formula is proved contained under hypotheses for boxes of `s`, zeta,
zeta derivative, digamma, `log π`, the contour parameter, and positive squared-norm boxes. The
closed-arc endpoint adapter is currently only for `n=0` and still assumes every component box and
every comparison with the Arb endpoints. It does not prove those inputs; `n=1,2` plus all component
enclosures remain needed for the first determinant. See the evidence memo and exact list in
`OPEN_OBLIGATIONS.md`.

### Latest C3 coefficient-table bridge

`SigmaContour51TaylorCoefficientBridge.lean` proves
`contourTaylorCoefficient (deriv f) c k = (k+1) * contourTaylorCoefficient f c (k+1)` and
constructs the derivative Taylor polynomial interval from the same coefficient boxes used for
`f`. Its `contourTaylorCauchyValueAndDerivativeBoxes` theorem combines the function and derivative
Cauchy remainders to produce both boxes under one explicit set of analytic hypotheses. Its four
theorem audits report only `[propext, Classical.choice, Quot.sound]`. This matches the coefficient
reuse in `acb_series.zeta()` and removes duplicate coefficient data for ζ′.

The ζ coefficient boxes, Cauchy majorants, and arc displacement bounds are still not proved from
the Arb data. The 4096 residual pointwise inclusions (first `n=0,1,2`) and the independent
512-arc circle inclusion remain open. Their exact assumptions, rational residual margins, Arb to
Lean boundary, and C5 reuse limits are recorded in `OPEN_OBLIGATIONS.md` and `VALIDATION.md`.

### Latest geometry and composition step — 2026-11-09

`SigmaContour51ArcGeometry.lean` now proves continuous Lean boxes for the contour parameter
`z(u)` and its source parameter `s(u)` over every closed arc in either the 4096 or 512 uniform
partition, using the C5 rational π interval and certified `ComplexInterval.expCr`. The `log π`
component box is separately supplied by `SigmaContour51C5PiBridge.lean`. Both modules compile
under Lean 4.32 with warnings as errors; the geometry module has seven theorem audits, all using
only standard axioms. This closes the geometric containment fields of the C3 component record; it
does not provide ζ/ζ′/digamma boxes, denominator norm-square lower bounds, or comparisons with Arb
integrand endpoints.

The external Arb state remains 512 arcs for `‖R‖<0.746413<4/5` and 4096 arcs for all six residual
integrals. The exact Lean residue identity still identifies `e_n=H_n-P_n` with the normalized
integral of the original source kernel. The material C2 tail and Taylor/Cauchy evaluator remainder
are distinct. No unconditional residual sign, circle bound or central positivity is established.

`SigmaContour51Arb512ComponentComposition.lean` now proves that a complete per-arc set of
component boxes, positive norm-square intervals and an exact rational comparison of the composed
response box implies the 512-arc Arb endpoint inclusion. Supplying such records for all arcs implies
the existing response-inclusion premise used to derive `hR`. The implication is compiled and
audited; the analytic records themselves remain unproved.

The next minimum is the Lean component-box construction from exact ζ Taylor coefficients and
Cauchy data, with digamma boxes and rational comparisons to the exported endpoints, first on all
4096 arcs for `n=0,1,2`. It yields the already compiled `1/10^9` determinant margin only after the
universal inclusion is proved. For the full target, all six residual transfers remain necessary;
the 512-arc circle transfer now has a compiled component-box adapter but still needs its analytic
records. C5's Bernoulli table and node lists were not rerun; displaced C5 boxes still have no
quantitative transport to `d=0`.
