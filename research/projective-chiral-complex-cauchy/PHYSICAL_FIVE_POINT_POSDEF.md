# Checkpoint — fifth physical C2 Cauchy–Pick radial block, strict positivity

Date: 2026-11-17
Branch: task/gon-c2-pick-five-schur-20261117
Base: GoN #338, commit 7388dce. Stacked on #337/#336/#335/#334.
No merge; no modification of the original CSA or other worktrees.
Cross-repository proof is kept in a research comparator module rather than
changing the GoN Lake manifest.

## Main NEW results (Lean 4.32, fully checked)

research/material-central-calibration/PhysicalPickFiveFinal.lean:

  physicalC2RadialPickMatrix_five_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      (physicalC2RadialPickMatrix k 5).PosDef

  physicalC2RadialDefectMatrix_five_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      (physicalC2RadialDefectMatrix k 5).PosDef

The five heights are exactly
  z_j = i (j+1)/(k+1),  j = 0,1,2,3,4.

The proof is EVENTUAL as k→∞, with no explicit lower bound on k.
For sufficiently large k, all nonzero complex coefficient vectors in
ℂ^5 have strictly positive Pick and chiral defect quadratic forms.

This is not a theorem about arbitrary points in the half-plane or the
Schur class globally. Nor does it prove all-order Hankel positivity or RH.

## Source-first provenance

Second-difference material C2 bracket → actual seed/centers/legs →
L¹/L² gradients and full physical Green return → camera factor →
archimedean completion → differentiated full state/companion →
complex native identification as an independently proved germ →
Cauchy–Pick and Hermite–Biehler quotient.

Native moments enter the proof ONLY as previously certified signs of
confluent Taylor coefficients. No source is redefined by a zeta/theta or
a target Gram; the exact physical identification remains that of #335.

## Step A — the previously missing *even* 3×3 certificate

New cross-repo module:
  research/material-central-calibration/PhysicalPickFiveSourceHankel.lean

  canonical_native_unshifted_hankel_three_posDef
  canonical_native_unshifted_hankel_three_det_pos

These are derived from the existing GoN material Cholesky:
  CarryMaterialSourceFactorComparison.material_hankel_cholesky_four_identity
  CarryMaterialSourceFactorComparison.material_hankel_cholesky_four_det_pos

The original material residual and its three positive pivots factor the
ACTUAL canonical real Hankel H4 = C*Cᵀ. This is PSD, and det(C)>0 makes
det(H4)>0; consequently H4 is positive definite. Its leading principal
H3 is positive definite, hence det(H3)>0.

This does not identify the full physical L² carrier Gram with the
canonical Hankel (a separately open question); it uses the exact
previously proved finite-dimensional factor as a *sign certificate*.

## Step B — parity split of the fifth confluent limit

  GeometryOfNumbers/Analysis/CarryMaterialPickFiveParity.lean:
    c2_five_parity_determinant.

The limit matrix is

  [h0,  0, h1,  0, h2]
  [ 0, h1,  0, h2,  0]
  [h1,  0, h2,  0, h3]
  [ 0, h2,  0, h3,  0]
  [h2,  0, h3,  0, h4].

A faithful simultaneous row+column reindexing groups even 0,2,4 and
odd 1,3. The Lean determinant proof gives

  det C5 = det([h0 h1 h2; h1 h2 h3; h2 h3 h4])
          * det([h1 h2; h2 h3]).

The even 3×3 is strictly positive by Step A; the odd shifted 2×2 by
the existing CSA eighth-order theta certification:
  canonicalCompletedNativeShiftedHankel_two_det_pos.

  research/material-central-calibration/PhysicalPickFiveNative.lean:
    polarizedGreenMomentCoefficient_five_det
    canonicalCompletedNativeRadialFivePointDifferenceMatrix_tendsto
    canonicalCompletedNativeRadialFivePointDifferenceMatrix_det_tendsto
    canonicalCompletedNativeRadialFivePointDifferenceMatrix_det_eventually_re_pos.

The last theorem is a strictly positive REAL determinant for the
normalized fifth confluent Cauchy–Pick matrix, for sufficiently fine
radial steps, with the existing all-order analytic difference limits.

## Step C — no crossing is dropped

  research/material-central-calibration/PhysicalPickFiveCongruence.lean:
    completedGreenFivePointDifference_congruence
    canonicalCompletedNativeRadialFivePointDifferenceMatrix_eq_congruence.

For a nonzero complex step h, the exact coefficient transform is:

  [1, -1/h,  1/(2h²), -1/(6h³),  1/(24h⁴)]
  [0,  1/h, -1/h²,    1/(2h³), -1/(6h⁴)]
  [0,   0,   1/(2h²), -1/(2h³), 1/(4h⁴)]
  [0,   0,    0,      1/(6h³), -1/(6h⁴)]
  [0,   0,    0,       0,       1/(24h⁴)].

Lean proves, for an ARBITRARY two-variable complex kernel and all
25 ordered crossings (p,q), including those involving fourth
differences:

    D5(h) = T5(h)ᴴ * K5(h) * T5(h).

No artificial metric, lost conjugation or diagonal-only comparison.
The focused Lean proof uses an explicit finite computation with
increased maxHeartbeats; no assumption or axiom is added.

## Step D — sign in the ORIGINAL Cauchy–Pick matrix

  research/material-central-calibration/PhysicalPickFiveSign.lean:
    canonicalCompletedNativeRadialDslopeSampleMatrix_five_det_eventually_re_pos

The determinant identity
    det D5 = normSq(det T5)*det K5
transports the strict sign to the original native dslope sample.
The factor normSq(det T5) is nonnegative by algebra; no unitary
claim is made for the forward-difference coordinates.

## Step E — physical Schur 4+1 and chiral strictness

  GeometryOfNumbers/Analysis/CarryMaterialPickFiveSchurCriterion.lean:
    hermitian_fin_five_posDef_of_leading_posDef_det_pos.

This generic Hermitian criterion is proved using Schur complement
and exact reindexing: if the true leading 4×4 block is PD and
the full 5×5 determinant is positive, the full 5×5 is PD.

In PhysicalPickFiveFinal.lean:
- the leading 4×4 physical Pick principal block is exactly the
  physical Pick4 certified in GoN #338;
- the physical complex germ C2↔Native is uniform over each fixed
  five-point family, so the native determinant sign transports;
- hermiticity is proved from the actual C2 complex divided response;
- the invertible physical Hermite–Biehler gauge of #335 transfers
  strict positivity to the chiral multiplier defect.

## Validation boundary

Lean 4.32 focused and cross-repo with -DwarningAsError=true;
#prints depend only on propext, Classical.choice, Quot.sound.
No sorry, no custom axiom, no blanket PosDef premise and no merge.
Reproduce with research/projective-chiral-complex-cauchy/validate-physical-five.sh
and the CSA root directory as argument.

The next sixth-order gate has an even 3×3 and an ODD shifted 3×3
in the confluent limit. The new independent sign would be the
shifted third Hankel determinant; the fifth-order result does not
establish this sixth-order sign automatically.
