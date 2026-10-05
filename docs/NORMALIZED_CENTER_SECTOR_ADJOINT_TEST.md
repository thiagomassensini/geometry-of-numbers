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
