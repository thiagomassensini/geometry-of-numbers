# Physical C2 radial Cauchy–Pick 9×9: source even Schur sign

Date: 2026-11-17. Branch task/gon-c2-pick-nine-schur-20261117.
Base GoN #342 commit 41a0179, stacked on #341 and earlier GoN chain.
No merge, previous worktrees untouched.

## Exact source genealogy

Original centered C2 bracket → physical centres, legs, seed,
depth, return → finite TFVD/Parseval and full GG/GR/RG/RR
crosses → camera → native/Genuine complex comparison →
archimedean completion → projective-chiral Cauchy–Pick →
Hermite–Biehler physical defect.

Bracket, Genuine synthesis and completed F are different objects.
The physical Pick is not defined as a canonical Hankel or
an arbitrary Gram chosen for positivity.

## Ninth sign: the source EVEN channel

Original native coefficient a_j = nativeSourceOddBoundaryCoefficient j
= 2 * primeDepthGeometricMoment j = 2 h_j, where h is the
canonical completed-native response moment sequence.
Our NEW matrix nativeSourceNineEvenRawMatrix(i,j)=a_(i+j)
only indexes the pre-existing source coefficients.

Exact new Lean:
  canonicalCompletedNativeUnshiftedHankel_five_posDef
  canonicalCompletedNativeUnshiftedHankel_five_det_pos
  canonicalCompletedNativeUnshiftedHankel_five_factor
  canonicalCompletedNativeUnshiftedHankel_five_det_eq_factor_sq

These follow from the EXISTING material source certificates
  CarryCriticalSource.even_source_five_posDef
  CarryCriticalSource.restoredEvenFiveFactor_identity
  CarryCriticalSource.restoredEvenFiveFactor_det_pos.

In particular H5=C5*C5^T with det C5>0. This is original
source Cholesky, not a synthetic positive metric.

Exact NEW raw determinant sign:
  nativeSourceNineEvenRawMatrix_eq_two_hankel_five
  nativeSourceNineEvenRawDiscriminant_eq_thirtytwo_hankel_five_det
    delta9_even = 32 det H5 > 0.

The previous four-even discriminant was already an original
CSA source polynomial. NEW exact bridge:
  nativeSourceSevenEvenDiscriminant_eq_nativeHankel_four_det
  nativeSourceSevenEvenDiscriminant_eq_sixteen_hankel_four_det
    delta7_even = 16 det H4 > 0.

Consequently:
  nativeSourceNineEvenRawRatio_eq_two_hankel_ratio
    delta9_even/delta7_even = 2 det H5/det H4 > 0.
  nativeSourceNineEvenRawDiscriminant_pos
  nativeSourceNineEvenRawRatio_pos.

This new determinant of the raw five-even coefficient block
is newly named here, not misleadingly claimed to be a
previously named nine-source discriminant in CSA.

The ORIGINAL inverse-coupled fifth-even Schur margin is
  sigma = sourceMomentSchur h 0 4
        = h8 - b^T H4^(-1) b, b_i=h_(i+4).
Its positivity was previously certified from the source in
  CarryCriticalSource.fifth_even_pivot_pos.

The existing exact CSA sourceMomentSchur_sewing is
specialized to native scaling a_j=2h_j:
  nativeSourceNineEvenOriginalQuadratic_sewing:
    2 Q5(snoc x t) =
      2 Q4(x+t H4^(-1)b) + 2 sigma * t^2.
  nativeSourceNineEvenCriticalDirection_energy:
    2 Q5(snoc(-H4^(-1)b) 1) = 2 sigma.
These formulae retain all old-new source crosses and the
full inverse coupling. NEW additional Lean, proved via
Mathlib's exact block Schur determinant theorem:

  nativeEvenFiveDet_eq_four_det_mul_sourceSchur
      det H5 = det H4 * sigma;
  nativeSourceNineEvenRawRatio_eq_twice_originalPivot
      delta9_even / delta7_even = 2 * sigma.

Thus the raw determinant ratio is proven IDENTICAL to the
actual inverse-coupled original source residual. The factor
two is the source coefficient normalization, not a new metric.
No symbolic 5×5 determinant expansion is used.

## The complete physical boundary, not just the even sector

The original source energy is
  nativeSourceFiniteBoundaryEnergy 9 x.
The prior source theorem CarryThetaPattern.ten_boundary_positive
certifies the FULL polarized ten-source energy from source H5/K5,
and CSA proved nativeSourceFiniteBoundaryEnergy_snoc_zero.
Consequently NEW Lean:
  nativeSourceNineCompleteBoundaryEnergy_pos
for every nonzero complex nine-source vector. Exact zero-padding
retains all physical GG/GR/RG/RR crosses; no positive
replacement form is introduced.

The old GoN return estimate also gives NEW explicit specialization:
  nativeSourceNineReturn_eventually_contractive
from CarryThetaPattern.return_contractive_through_ten 9.
This is fixed-source return control, not arbitrary-height global
Schur-class contractivity.

## Radial 9×9 Pick and projective-chiral HB defect

The original canonical radial heights are
  z_j=i(j+1)/(k+1), j=0,...,8.

Exact simultaneous parity reindexing of the 81-entry confluent
matrix proves
  c2_nine_parity_determinant:
    det C9=det H5*det K4 > 0.
H5 is source-positive above, K4 is source-positive in #342,
where the original eight-odd source discriminant was proved
to equal 16 det K4.

The existing analytic CSA two-step radial limit gives the
eventual strictly positive determinant of the normalized
nine-point finite-difference kernel.

The exact binomial transport was ALREADY general in all N in CSA
(CompletedNativeChiralPickHankel.lean):
  completedGreenComplexShiftedKernelForwardDifferenceMatrix_apply.
For fixed N=9 it is specialized, NOT redefined as a new metric:
  completedGreenNinePointDifference_congruence
    D9 = T9^* K9 T9,
with every one of the 81 crossings and arbitrary complex kernel.
T9 uses coefficients (-1)^(p-i) choose(p,i)/(p! h^p).
Determinants are transported to the original dslope sample
matrix and then to the physical C2 Pick by the previously proved
source-first complex germ equality.

The true physical 8×8 principal block is positive by GoN #342.
The new generic Hermitian Schur 8+1 theorem is
  hermitian_fin_nine_posDef_of_leading_posDef_det_pos.

Final NEW Lean:
  physicalC2RadialPickMatrix_nine_eventually_posDef
  physicalC2RadialDefectMatrix_nine_eventually_posDef.
The defect is transferred through the old invertible physical
HB multiplier gauge, preserving every complex direction.

## Scope and reproducibility

Lean 4.32, -DwarningAsError=true, no sorry, admit, native_decide,
custom axiom, or changes in historical source definitions.
Only propext, Classical.choice, Quot.sound appear in the
new source theorem axiom prints.

Reproduction script:
  research/projective-chiral-complex-cauchy/validate-physical-nine.sh
  /home/thlinux/carry-self-adjoint-operator.

Only fixed order N=9, eventually in radial k, no explicit
threshold. Not arbitrary-position Schur-class inequality,
uniform all-order positivity, fixed infinite Gram or RH.

For N=10, both H5 and K5 already have separate finite source
certificates. No N=10 physical transport is claimed here.
