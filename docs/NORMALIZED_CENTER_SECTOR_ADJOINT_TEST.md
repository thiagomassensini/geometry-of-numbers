# Normalized center sector and adjoint test

## Question and provenance

Does geometric incoming center reconstruction agree with the adjoint of outgoing leg synthesis? The source is the current standard seeded material Hilbert space; the target is the current physical-edge l2. Gaps and finite prefixes predate this construction. No moments, amplitudes fitted to a readout, free weights or new metric enter it. All inputs are local definitions and Mathlib.

## Increment 1: geometric factorization

For each cell, write a_k=leftGap and b_k=rightGap. Define

$$q_k=\sqrt{a_k^2+b_k^2}>0,\qquad u_{k,a}=\frac{gap_{k,a}}{q_k}.$$

Strict log monotonicity proves q_k positive; the two u squares sum exactly to 1. `baseTwoCenterLegSynthesis` is an isometry from `BaseTwoCenterL2 = l2(N,Complex)` to `PhysicalEdgeL2`, with coordinate u_{k,a} h_k.

`baseTwoNormalizedCenterReconstructionRaw` multiplies the existing finite center reconstruction by q_k. Equality of row energies gives exact equality of infinite energies with the existing bounded K. Actual summability and l2 membership follow from K. `baseTwoNormalizedCenterReconstruction` is its ContinuousLinearMap packaging with bound 4. Hardy is not reproved.

`baseTwoCenterCoupling_factorization` proves K=S T as an equality of ContinuousLinearMaps. `baseTwoNormalizedCenterReconstruction_norm` proves norm T(y)=norm K(y). On the concrete orbit, `baseTwoNormalizedCenterReconstruction_concrete` gives q_k * criticalMaterialSample t (baseTwoCenter k).

The unnormalized center sample sequence is not asserted to be l2. No claim of symmetry follows from this factorization. The next increment tests T_phys against S.adjoint with the existing right-edge delta.

All public definitions and theorems are registered with #assert_analysis_axioms and #print axioms. Allowed footprint: [propext, Classical.choice, Quot.sound]. Validation and integrated commit references follow below.

Increment 1 validation: module/scoped audit/Analysis/Analysis.Audit `--wfail`, Analysis/Foundation/Geometry scripts and placeholder scan all exit 0. New capstones print [propext, Classical.choice, Quot.sound]. Foundation remains empty-footprint. Status of this increment: PASS_NORMALIZED_CENTER_SECTOR_FACTORIZATION.


## Increment 2: standard adjoint and exact mismatch

The formula `baseTwoCenterLegSynthesis_adjoint_apply` is proved from the standard Hilbert adjoint identity tested on a single center coordinate, whose synthesis is exactly two physical deltas:

$$(S^\dagger x)_k=\sum_{a<2}u_{k,a}x_{k,a}.$$

Real geometric coefficients eliminate conjugation. `baseTwoCenterLegSynthesis_adjoint_comp_self` reuses `LinearIsometry.adjoint_comp_self`, so S.adjoint S=I.

`baseTwoPhysicalToSeeded` is a public name for the already constructed zero-seed physical isometric embedding. `baseTwoPhysicalCenterReconstruction` is T composed with that map, not defined using the adjoint. `baseTwoPhysicalCenterSelfCoupling_factorization` preserves exactly K_pp=S T_phys.

The existing first-cell calculation proves `baseTwoPhysicalCenterReconstruction_deltaRight_zero`. This uses the already certified causal prefix: physical edge 3 does not enter the center-4 prefix. The other map gives

$$(S^\dagger\delta_R)_0=\frac{\log5-\log4}{\sqrt{(\log4-\log3)^2+(\log5-\log4)^2}}\ne0.$$

`baseTwoPhysicalCenterReconstruction_ne_legSynthesis_adjoint` is the main capstone. Incoming reconstructed center and outgoing leg return are not the same adjoint role. This is a representation mismatch only, not a no-go for the full clock or theory.

The minimal next question is how geometry separates incoming reconstruction from outgoing return (two center sectors or a graph/return realization). Neither option is selected or constructed here. No claim that one of them suffices has been proved.

Increment 1 integrated commit: `3843d939f6e7be5533a9f1a9627d7834e090d9cc`.

Increment 2 validation: module/scoped audit/Analysis/Analysis.Audit `--wfail`, Analysis/Foundation/Geometry scripts and placeholder scan all exit 0. The explicit adjoint formula, K_pp factorization and adjoint mismatch capstones print only [propext, Classical.choice, Quot.sound]. Status: PASS_CENTER_SECTOR_ADJOINT_MISMATCH.
