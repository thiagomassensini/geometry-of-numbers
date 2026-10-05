# Bounded geometric center coupling

## Increment 1: sampled Hardy bound

For every complex sequence g and cutoff N, `baseTwoSampledHardy_finite` proves

$$\sum_{k<N}rac{|\sum_{j<4k+3}g_j|^2}{(4k+3)^2}\le4\sum_{j<4N+3}|g_j|^2.$$

Weighted Cauchy-Schwarz uses sqrt(j+1). The reciprocal square-root prefix telescopes to 2 sqrt(m). For m>=3, the sampled reciprocal step is bounded by 2(1/sqrt(m)-1/sqrt(m+4)). `baseTwoSampledHardy_tail` includes the exact condition j<4k+3. A decreasing potential treats the first admissible sample without a choice or ceil API.

This is only the required subsequence theorem, not a general Hardy theory. No moment, symmetry, adjoint or block follows from it. The physical first-cell nonsymmetry remains unchanged.

Public capstones are registered with `#assert_analysis_axioms` and `#print axioms`; expected footprint is contained in [propext, Classical.choice, Quot.sound]. Build/audit commands are recorded after execution below.

Increment 1 validation: `lake build --wfail GeometryOfNumbers.Analysis.BaseTwoSampledHardy GeometryOfNumbers.Analysis.BaseTwoSampledHardyAudit GeometryOfNumbers.Analysis GeometryOfNumbers.Analysis.Audit`, Analysis/Foundation/Geometry audit scripts, placeholder scan and `git diff --check`: all exit 0. Both public capstones print exactly [propext, Classical.choice, Quot.sound].
