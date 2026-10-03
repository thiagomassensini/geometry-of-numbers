# Base two: exact whole-cell head/tail completion

STATUS: `PASS_EXACT_HEAD_TAIL`

Base: `9ac65f62f714b276155617f4646fa7911727f7e0`.
Branch: `base-two-exact-head-tail`.
Namespace: `GeometryOfNumbers.Analysis.BaseTwoCompletion`.

## Internal material provenance

The existing, unchanged `log_eq_sum_primeCarryVoice` proves

$$
\log n=\sum_{p\in n.\mathrm{factorization.support}}\mathrm{primeCarryVoice}(n,p).
$$

The finite coordinate `j : Fin N` represents the material integer `j.val+1`.
`criticalMaterialSample_eq_finiteMaterialOrbit` identifies the auxiliary pointwise
extension literally with `finiteMaterialOrbit N t (historicalInitialState N) j`.
For positive material integers the existing sample is

$$
f_t(n)=n^{-1/2}\exp(-it\log n).
$$

`criticalMaterialSample_eq_rpow_phase` and `criticalMaterialSample_eq_cpow` prove
these representations. There is no second clock. This is the historical material
amplitude, not the depth amplitude of the modern C2 source.

## Geometric cell and exact finite head

`baseTwoCenter` uses the existing `historicalCameraPeriod 2`.
`baseTwoLeftLeg` and `baseTwoRightLeg` use the existing integer `leftLeg`,
`rightLeg` and `positiveCameraRadius (0 : Fin 1)` APIs. The geometry yields

$$
\mathrm{left}_k=4(k+1)-1,\quad
\mathrm{center}_k=4(k+1),\quad
\mathrm{right}_k=4(k+1)+1.
$$

The corresponding theorems are `baseTwo_leftLeg_eq`, `baseTwo_center_eq`,
`baseTwo_rightLeg_eq`. This is the existing exceptional aligned camera-2
convention, not an identification with `oddCameraCapacity 1`.

$$
B_k(t)=f_t(\mathrm{left}_k)-2f_t(\mathrm{center}_k)+f_t(\mathrm{right}_k),
\qquad
\mathrm{Head}_M(t)=f_t(1)+\sum_{k<M} B_k(t).
$$

`baseTwoCriticalCenterCell_eq_causalUnitBracket` identifies the existing
second-difference stencil. The seed remains separate and equals one.

The required literal theorem is `baseTwoFiniteHead_eq_historicalFiniteHeadReadout`:

$$
\mathrm{Head}_M(t)=\mathrm{finiteHeadReadout}
  (\mathrm{historicalCameraWeights}\ 2\ M)
  (\mathrm{finiteMaterialOrbit}\ N\ t\ (\mathrm{historicalInitialState}\ N)),
\qquad N=4M+1.
$$

The proof expands existing weights, exchanges finite sums and selects each
material coordinate; it does not assume an interpretation of the readout.

## Absolute summability of complete cells

Write $z_t=-\tfrac12-it$. For positive real points the sample is $x^{z_t}$.
Two mean-value bounds on the forward difference give the complete-cell bound

$$
|B_k(t)|\le |z_t(z_t-1)|(k+1)^{-5/2}.
$$

The local theorem is `baseTwoCriticalCenterCell_norm_le`. This preserves the
cancellation of the whole cell; it is not a sum of separate leg estimates.
Mathlib's summable real-power series then gives
`summable_norm_baseTwoCriticalCenterCell` and
`summable_baseTwoCriticalCenterCell`, for every real $t$.
No uniform-in-time bound or differentiation of the infinite tail is claimed.

## Derived tail and cutoff independence

$$
\mathrm{Tail}_M(t)=\sum_{k\ge0} B_{k+M}(t),\qquad
\mathrm{Signal}(t)=f_t(1)+\sum_{k\ge0} B_k(t).
$$

These are `baseTwoCriticalCompleteTail` and `baseTwoCriticalCompleteSignal`.
`baseTwoCriticalCompleteTail_hasSum` verifies the shifted complete-cell series.
No external tail parameter is consumed.

`baseTwoFiniteHead_add_completeTail` proves exactly

$$
\mathrm{Head}_M(t)+\mathrm{Tail}_M(t)=\mathrm{Signal}(t)
$$

by `Summable.sum_add_tsum_nat_add`. `baseTwoCompletedSignal_cutoff_independent`
follows by rewriting this identity. `baseTwoHistoricalReadout_add_completeTail`
exposes the identity at the existing finite readout interface.

## Endpoint audit

For $M>0$, the last retained right leg is $4M+1$, exactly the head horizon.
The first omitted complete cell is $(4M+3,4M+4,4M+5)$.

`baseTwo_endpoint_incidence` proves that every omitted left leg lies strictly
beyond the head horizon. `baseTwo_firstOmittedCell_points` records the triple;
`baseTwo_retained_cell_in_head` bounds retained cells. At $M=0$ the head is the
seed at material 1. There is no shared C2 endpoint, dangling or duplicated leg.
The historical shared-endpoint theorem for even cameras at least 4 does not
apply to camera 2.

## Existing clock jets

`baseTwoFiniteHead_iteratedDerivative` reuses the unchanged
`finiteHeadReadout_iteratedDerivative`. `baseTwoFiniteHead_normalizedClockJet`
reuses the unchanged `finiteClockJets_to_head` and proves

$$
\mathrm{historicalFiniteHeadCoefficient}_r
=\frac{1}{r!}\,\mathrm{iteratedDeriv}_r(\mathrm{Head}_M)(0).
$$

The existing jets are precisely jets of this geometric head. The infinite tail
jet tower is not derived; the downstream finite ledger's external `tail`
parameter is not replaced in this round.

## Historical comparison: read-only, no dependencies

Only the two permitted files were consulted:

| Reference | Revision | File SHA-256 |
| --- | --- | --- |
| `primos`, PR [#3](https://github.com/thiagomassensini/primos/pull/3), `CPFormal/Analytic/CpGenuineFirstCutoffTail.lean` | merge `6dcecd52ff0e46ea7599892ba1d1ded62e5dd4ab` | `3b3a57bed0e6c600bde81ff8b02d996416b14f829e5ee8ef01db95e61db52493` |
| `native-carry-c3-crosswalk`, `NativeCarryC3Crosswalk/GeometricCutoffCompleteness.lean` | `d9e9e3a7469cb2a95ad3a07d08d0c1a860377ec0` | `b58a7102ecda16d808d1766ac153157406684b05bf9456738a602583b6944d04` |

The `primos` local HEAD was `8c4b7fdf65a49d1d0febe8193d56e2cfb2191260`;
the allowed file was verified byte-identical to its PR-merge version.
Comparison identities: `bracketedDirichletChart_eq_finite_add_cutoffTail`,
`c2_complete_horizon`, `included_center_has_both_legs_in_window`,
`last_right_leg_eq_finiteCameraWindow`, `complete_head_add_complete_center_tail`.
`even_endpoint_records_head_tail_incidence` requires camera at least 4 and was
not transplanted to camera 2.

All proofs use current GeometryOfNumbers and Mathlib APIs. Neither historical
package is imported or added to the dependency configuration. No old worktree
was used as a source.

## Kernel audit and validation

All 31 public definitions/theorems have rejecting axiom guards and
`#print axioms` in the dedicated audit and central `Analysis/Audit.lean`.
Capstone footprint: `[propext, Classical.choice, Quot.sound]`;
all other new declarations are within the same allowed set.
No `sorry`, `admit`, new axiom or `unsafe`.

All following checks passed before integration (including the explicit kernel
audit and axiom guards):

```bash
lake build --wfail GeometryOfNumbers.Analysis.BaseTwoExactHeadTailCompletion
lake build --wfail GeometryOfNumbers.Analysis.BaseTwoExactHeadTailCompletionAudit
lake build --wfail GeometryOfNumbers.Analysis
lake build --wfail GeometryOfNumbers.Analysis.Audit
bash scripts/audit-foundation.sh
bash scripts/audit-geometry.sh
bash scripts/audit-analysis.sh
git diff --check
```

Foundation, Geometry, dependency files, `FiniteMaterialClockJets` and the four
protected finite-height modules are unchanged.

## Scope preserved

This closes the exact complete-cell tail of the existing historical critical
material head. It does not identify the modern provenance-correct C2/Green
source with historical completed scalarization, replace the downstream `tail`
argument, derive tail jets, or alter moments or finite height operators.

The existing material log/prime carry voice theorem remains unchanged.
The geometric conclusion is exactly: the finite material-clock head is a prefix
of the same absolutely summable complete bracket-cell family whose derived
omitted-cell tail completes it independently of cutoff.
