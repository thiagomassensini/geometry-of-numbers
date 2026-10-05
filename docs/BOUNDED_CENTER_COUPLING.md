# Bounded geometric center coupling

## Increment 1: sampled Hardy bound

For every complex sequence g and cutoff N, `baseTwoSampledHardy_finite` proves

$$\sum_{k<N}rac{|\sum_{j<4k+3}g_j|^2}{(4k+3)^2}\le4\sum_{j<4N+3}|g_j|^2.$$

Weighted Cauchy-Schwarz uses sqrt(j+1). The reciprocal square-root prefix telescopes to 2 sqrt(m). For m>=3, the sampled reciprocal step is bounded by 2(1/sqrt(m)-1/sqrt(m+4)). `baseTwoSampledHardy_tail` includes the exact condition j<4k+3. A decreasing potential treats the first admissible sample without a choice or ceil API.

This is only the required subsequence theorem, not a general Hardy theory. No moment, symmetry, adjoint or block follows from it. The physical first-cell nonsymmetry remains unchanged.

Public capstones are registered with `#assert_analysis_axioms` and `#print axioms`; expected footprint is contained in [propext, Classical.choice, Quot.sound]. Build/audit commands are recorded after execution below.

Increment 1 validation: `lake build --wfail GeometryOfNumbers.Analysis.BaseTwoSampledHardy GeometryOfNumbers.Analysis.BaseTwoSampledHardyAudit GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit`, Analysis/Foundation/Geometry audit scripts, placeholder scan and `git diff --check`: all exit 0. Both public capstones print exactly [propext, Classical.choice, Quot.sound].


## Increment 2: arbitrary-input bounded operator

The source remains `BaseTwoSeededMaterialHilbert = WithLp 2 (Complex x MaterialEdgeL2)`; target is the existing `PhysicalEdgeL2`. The raw coordinates remain log-gap times seed plus the finite material-edge prefix. No coordinate is redefined from the orbit defect.

`baseTwoCenterLogGap_bound` gives both gaps between 0 and 1/(4k+3). A further elementary reciprocal telescope gives `baseTwoCenterCoupling_seed_finite` and `baseTwoCenterCoupling_seed_tsum`:

$$\sum_k(4k+3)^{-2}\le1.$$

The two sides and $|z+S|^2\le2|z|^2+2|S|^2$ give

$$\sum_{k<N, a<2}|K_{raw}(z,g)(k,a)|^2\le4|z|^2+16\|g\|^2\le16\|(z,g)\|^2.$$

The nonnegative prefix bound proves actual summability (`baseTwoCenterCouplingRaw_summable_sq`) and `Memlp` (`baseTwoCenterCouplingRaw_memℓp`). `baseTwoCenterCouplingL2` uses these proofs to bundle the same raw function. `baseTwoCenterCouplingL2_norm_le` proves

$$\|K(z,g)\|\le4\|(z,g)\|.$$

`baseTwoCenterCouplingOperator` is its `mkContinuous` packaging. The mandatory theorem `baseTwoCenterCouplingOperator_concrete` identifies its image on `baseTwoConcreteSeededGradientState t` with the pre-existing `baseTwoPhysicalCenterClockDefectL2 t`. The defect is not duplicated or modified.

The finite nonsymmetry remains valid. Boundedness alone does not imply symmetry. Auxiliary adjoint/block symmetry, center-sector dilation, Naimark and canonical moments are outside this round.

Commit already integrated for increment 1: `0e2d7d81753348a538e4745a0668edc020570c36`.

Increment 2 validation: new module, scoped audit, Analysis and Analysis.Audit all pass `lake build --wfail`; Analysis/Foundation/Geometry scripts, placeholder scan and `git diff --check` all exit 0. The new public capstones have exactly [propext, Classical.choice, Quot.sound]. Status of this increment: PASS_BOUNDED_CENTER_COUPLING.
