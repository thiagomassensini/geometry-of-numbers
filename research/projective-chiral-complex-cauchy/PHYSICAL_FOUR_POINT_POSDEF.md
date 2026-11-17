# Physical C2 Cauchy–Pick 4×4: strict radial positivity

Date: 2026-11-17
Branch: task/gon-c2-pick-four-schur-20261117
Parent GoN PR: #337; stacked on #336/#335/#334.
No merge; no new shared Lake dependency.

## Main Lean results

In research/material-central-calibration/CanonicalComparison.lean:

  physicalC2RadialPickMatrix_four_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      (physicalC2RadialPickMatrix k 4).PosDef

  physicalC2RadialDefectMatrix_four_eventually_posDef :
    ∀ᶠ k : ℕ in atTop,
      (physicalC2RadialDefectMatrix k 4).PosDef

The four heights are the canonical radial grid
  z_j = i (j+1)/(k+1), j=0,1,2,3,
for sufficiently large k, without a numerical bound on k.
The second result certifies strict positive quadratic energy of the
HB multiplier defect on every nonzero coefficient vector in ℂ⁴.

## Source-first chain

Genuine centered C2 bracket → physical material gradients (L¹/L²),
seed and complete return → camera factor → archimedean dressing →
differentiated full Hilbert vector → two chirality channels →
Cauchy–Pick kernel and source Hermite–Biehler quotient.

The physical source is not defined as Native, theta, zeta or Hankel:
the identification in a complex germ is a separate theorem from
GoN #335. Signs of canonical low-order moments are separate input
theorems of CSA, not new geometric positivity assertions.

## Certificate details

1. GeometryOfNumbers/Analysis/CarryMaterialPickFourParity.lean:
   c2_four_parity_determinant.

   The four-by-four confluent coefficient array is

      [h0,  0, h1,  0]
      [ 0, h1,  0, h2]
      [h1,  0, h2,  0]
      [ 0, h2,  0, h3]

   with exact determinant:
      (h0*h2-h1²)*(h1*h3-h2²).

   Both factors are strictly positive in existing CSA theorems:
     canonicalCompletedNativeHankel_two_det_pos
       (sixth-order theta certification)
     canonicalCompletedNativeShiftedHankel_two_det_pos
       (eighth-order theta certification).

2. research/material-central-calibration/PhysicalPickFourNative.lean:
   canonicalCompletedNativeRadialFourPointDifferenceMatrix_tendsto,
   polarizedGreenMomentCoefficient_four_det,
   canonicalCompletedNativeRadialFourPointDifferenceMatrix_det_tendsto,
   canonicalCompletedNativeRadialFourPointDifferenceMatrix_det_eventually_re_pos.

   The convergence is exact, with the original all-order analytic
   finite-difference tail and no sign postulate.

3. research/material-central-calibration/PhysicalPickFourCongruence.lean:
   completedGreenFourPointDifference_congruence,
   canonicalCompletedNativeRadialFourPointDifferenceMatrix_eq_congruence.

   The exact finite-difference transform is
      [[1, -1/h, 1/(2h²), -1/(6h³)],
       [0, 1/h, -1/h², 1/(2h³)],
       [0, 0, 1/(2h²), -1/(2h³)],
       [0, 0, 0, 1/(6h³)]].

   D4 = T4ᴴ * K4 * T4 is proved for ALL 16 entries and any
   complex-valued two-variable kernel at nonzero step h.
   No artificial positive metric or omitted cross terms.

4. research/material-central-calibration/PhysicalPickFourSign.lean:
   canonicalCompletedNativeRadialDslopeSampleMatrix_four_det_eventually_re_pos.

   det(D4) = normSq(det T4) * det(K4).
   Strictly positive real det(D4) and normSq >= 0 force
   Re(det K4)>0; no hidden isometry assumption.

5. GeometryOfNumbers/Analysis/CarryMaterialPickFourSchurCriterion.lean:
   hermitian_fin_four_posDef_of_leading_posDef_det_pos.

   A Hermitian 4×4 with a strictly PD leading 3×3 block and
   strictly positive determinant is PD (3+1 Schur), proven with
   exact block reindexing and the one-dimensional complement.

6. The external GoN–CSA comparator transports the N=4 radial
   native determinant sign back to the ACTUAL physical C2 Pick.
   The leading 3×3 physical block is strictly PD by GoN #337.
   Hermiticity follows from the source divided response, not from
   assumed PSD. The invertible physical HB gauge transports
   strict PD to the multiplier defect.

## Audit

Lean 4.32. Focused modules and cross-repo comparator compiled using
-DwarningAsError=true; axioms: propext, Classical.choice, Quot.sound.
No sorry, admit, custom axiom or new dependency; no merge.

## Scope

The result is LOCAL to the specified four-point radial samples and
eventual in the refinement k. No all-order / arbitrary-position PSD,
no global Schur-class contraction, no general Hankel theorem, no RH.

The fifth-order confluent parity split requires an unshifted even
3×3 determinant (indices 0,2,4), multiplied by the already certified
shifted odd 2×2 determinant (indices 1,3). Whether the even 3×3
certificate can be connected to this physical Pick family must be
checked independently; it does not follow from the fourth closure.
