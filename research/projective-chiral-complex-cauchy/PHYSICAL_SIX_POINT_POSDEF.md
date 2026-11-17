# GoN physical C2 radial 6×6 — source-first sign transport

Date: 2026-11-17
Branch: task/gon-c2-pick-six-schur-20261117
Base: GoN PR #339, commit d9b4af7; stacked on #338/#337/#336/#335/#334.
Draft checkpoint, six-direction gate now Lean-checked; no merge or edits in earlier branches.

## Source genealogy (unchanged)

Centered second difference C2 → physical legs, depth, seed and return
→ gradient L¹/L² and finite TFVD/Parseval → camera factor
→ genuine/native complex germ (previous GoN #335) → completion and
differentiated companion → two projective-chiral channels → Cauchy–Pick
and Hermite–Biehler quotient.

Neither the Pick nor the physical Hilbert state is DEFINED as a Hankel.
Independent, already-proved moment margins are *sign certificates*
transported along an already-proven complex identity.

## Sixth-order NEW sign: the odd 3×3 determinant

The previously proved CSA source theorem:
  nativeSourceSixOddDiscriminant_pos

is obtained from an order-12 raw theta integral certificate.
Its original coefficients obey:
  nativeSourceOddBoundaryCoefficient j = 2*h_j
by the native prime-depth comparison and recurrence uniqueness.

NEW independent exact Lean theorem:
  nativeSourceSixOddDiscriminant_eq_eight_shiftedHankel_three_det

  nativeSourceSixOddDiscriminant =
      8 * det [[h1,h2,h3],[h2,h3,h4],[h3,h4,h5]].

Consequently:
  canonicalCompletedNativeShiftedHankel_three_det_pos.

No sign is presumed of the physical 6×6 Pick or the desired Gram.
All factors, indices and the factor 8 are certified.

## Sixth-order EVEN sign

GoN #339 already derived:
  canonical_native_unshifted_hankel_three_posDef
  canonical_native_unshifted_hankel_three_det_pos

from the existing material source Cholesky factor H4 = C*Cᵀ
and det C > 0. This proof preserves the original canonical moments.

## Exact confluent parity splitting

The normalized sixth-order Cauchy–Pick moment matrix is:

  [h0,0,h1,0,h2,0]
  [0,h1,0,h2,0,h3]
  [h1,0,h2,0,h3,0]
  [0,h2,0,h3,0,h4]
  [h2,0,h3,0,h4,0]
  [0,h3,0,h4,0,h5].

New Lean lemma c2_six_parity_determinant:
  det C6 = det H3 * det K3
for the *exact simultaneous permutation* of the even/odd sectors,
without altering the matrix or canceling any crossing.

New analytic finite-difference lemmas:
  polarizedGreenMomentCoefficient_six_det
  canonicalCompletedNativeRadialSixPointDifferenceMatrix_tendsto
  canonicalCompletedNativeRadialSixPointDifferenceMatrix_det_tendsto
  canonicalCompletedNativeRadialSixPointDifferenceMatrix_det_eventually_re_pos.

Both factors are strictly positive by previously proved source signs.
The determinant of the normalized six-point finite-difference kernel
is therefore eventually strictly positive, for k sufficiently large.

## Algebraic transport, physical closure and remaining general gate

The Lean-proved congruence, preserving ALL 36 crossings and fourth/fifth
normalization coefficients, is:
  D6(h) = T6(h)ᴴ * K6(h) * T6(h),

for h ≠ 0 and ANY complex two-variable kernel. T6 uses all divided
differences from order 0 through 5, with factorial normalization
and the sample heights z_j = i (j+1)/(k+1), j=0,…,5.

The new Lean declarations are:
  completedGreenSixPointDifference_congruence
  canonicalCompletedNativeRadialSixPointDifferenceMatrix_eq_congruence.

The kernel-checked determinant transport gives
  det D6 = normSq(det T6)*det K6,
and hence Re det K6>0, certified by:
  canonicalCompletedNativeRadialDslopeSampleMatrix_six_det_eventually_re_pos.

The true physical C2 Pick leading principal 5×5 is positive by
GoN #339; Hermiticity is inherited from the *actual* physical
divided response. The generic Schur 5+1 theorem is proved:
  hermitian_fin_six_posDef_of_leading_posDef_det_pos.

The resulting final Lean theorems both PASS:
  physicalC2RadialPickMatrix_six_eventually_posDef
  physicalC2RadialDefectMatrix_six_eventually_posDef.

The physically constructed matrix equals the Native sample matrix
eventually by the independently proved complex germ comparison,
and the HB gauge is invertible at the regular radial heights.

Both final types assert PosDef EVENTUALLY in k for exactly N=6,
and both have #print axioms listing propext, Classical.choice,
Quot.sound only. Lean 4.32; -DwarningAsError=true; no sorry.

## Mathematical boundary

Everything is local in HEIGHT near 0, and eventual in k for a
FIXED sample size 6. No uniform k threshold over all N is proved.
No arbitrary-position Schur-class inequality, all-order positive
Gram identification, or Riemann hypothesis follows.

Do not confuse this radial six-point Pick with the separate
six-source/six-coordinate boundary energy, or the GoN sixth odd
source certificates at different dimensions and cutoffs.

## Audit reproducibility and next sixth/future order boundary

The executable reproduction script is:
  research/projective-chiral-complex-cauchy/validate-physical-six.sh
which verifies the shared toolchain/pins, builds Mathlib-backed
GoN parity/Schur modules, compiles all GoN--CSA comparator modules
from earlier stages and the sixth stage in dependency order, then
checks the printed axiom declarations.

The N=7 parity split will require an unshifted H4 determinant
(available as the material Cholesky4 certificate) and the same
shifted K3 determinant now established from the source. Although
these finite scalar signs are already known, the seven-point
finite-difference congruence and physical Schur step have NOT
been checked and are not implied automatically.
