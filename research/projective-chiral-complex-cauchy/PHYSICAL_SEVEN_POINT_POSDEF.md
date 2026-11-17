# GoN: physical C2 radial Cauchy–Pick 7×7 — source-first transport

Date: 2026-11-17
Branch: task/gon-c2-pick-seven-schur-20261117
Base: GoN #340, c0ca520, stacked on #339/#338/#337/#336/#335/#334.
No merge. Other source branches and original CSA checkout unchanged.

## Provenance — the actual geometric source

Centered C2 second difference, seed, real centers and legs, depth and
physical L¹/L² gradients, full global return, TFVD/Parseval, camera and
archimedean dressing, completed vector companion and complex germ,
then projective-chiral Cauchy–Pick and Hermite–Biehler quotient.

The raw bracket, its Genuine synthesis and the completed F remain
different mathematical objects. The original Pick is not DEFINED
as a canonical Hankel Gram. We use already-proved source scalar
signs only AFTER the source-first complex identification from #335.

## Step A: both 7×7 confluent parity margins are positive

New Lean:
  canonical_native_unshifted_hankel_four_det_pos
  c2_seven_parity_determinant
  polarizedGreenMomentCoefficient_seven_det
  canonicalCompletedNativeRadialSevenPointDifferenceMatrix_tendsto
  canonicalCompletedNativeRadialSevenPointDifferenceMatrix_det_tendsto
  canonicalCompletedNativeRadialSevenPointDifferenceMatrix_det_eventually_re_pos

The limit of 7×7 normalized mixed finite-difference coefficients is:

  [h0,0,h1,0,h2,0,h3]
  [0,h1,0,h2,0,h3,0]
  [h1,0,h2,0,h3,0,h4]
  [0,h2,0,h3,0,h4,0]
  [h2,0,h3,0,h4,0,h5]
  [0,h3,0,h4,0,h5,0]
  [h3,0,h4,0,h5,0,h6].

The simultaneous parity permutation [0,2,4,6;1,3,5] proves EXACTLY

    det(C7) = det H4 * det K3,

  H4 = [h(i+j)] for i,j=0,1,2,3,
  K3 = [h(i+j+1)] for i,j=0,1,2.

The canonical even H4 = T4*T4ᵀ is a PREEXISTING material-source
Cholesky identity in GoN; its 4×4 triangular factor det T4 > 0.
The new source proof takes determinants to obtain det H4 > 0.
K3 > 0 is independently certified by GoN #340:
  nativeSourceSixOddDiscriminant = 8*det K3 > 0
using the original source-12 integral sign. Neither input assumes
the desired seventh Pick positivity.

The limit and its eventual strict determinant sign are then proved
from analytic shifted radial two-step forward-difference results in
CSA. This is a fixed dimension 7 result: no uniform N bound follows.

## Step B: exact seven-height stencil and physical transport

The seven sample heights are EXACTLY:
  z_j = i(j+1)/(k+1), j=0,1,2,3,4,5,6.

Rather than expand 49 separate matrix identities, the proof
reuses the EXISTING ALL-ORDER source theorem of CSA:

  completedGreenComplexShiftedKernelForwardDifferenceMatrix_apply.

This theorem already establishes the entire binomial
congruence entrywise for ANY N and any complex kernel.
Our specialized T7 is definitionally
  completedGreenComplexForwardDifferenceTransform h 7.
The source coefficient theorem is

  completedGreenComplexForwardDifferenceCoefficient.

The seven-point difference coefficient matrix T7(h) has entries

  T7(h)_(i,p) =
    (-1)^(p-i) * choose(p,i)/(p! * h^p) for i ≤ p,
    0 otherwise, h ≠ 0.

This is the native forward-difference coefficient, not a new
physical Hilbert-space metric. The specialized theorem is proven
via the general carrier, retaining ANY complex two-variable
kernel K, all 49 positions and the full conjugation:

   D7(h) = T7(h)ᴴ * K7(h) * T7(h),

with ALL 49 mixed crossings and conjugation/factorials through
degree p=6. It is NOT a diagonal or approximate interpolation.

The NEW Lean theorem
  completedGreenSevenPointDifference_congruence
is a strict consequence of the original all-N theorem,
plus the exact scalar coordinate rewrite on the radial grid;
  canonicalCompletedNativeRadialSevenPointDifferenceMatrix_eq_congruence
then aligns it with the existing native dslope sample matrix.

Then the original kernel sign follows from

   det D7 = normSq(det T7) * det K7.

This factor is nonnegative and cannot flip a strictly positive
real determinant. The original physical C2 Pick K7 is eventually
identified with the native K7 by the prior C2 complex germ theorem.

## Step C: exact 6+1 Schur and HB defect

Generic Lean theorem:
  hermitian_fin_seven_posDef_of_leading_posDef_det_pos

is built from the genuine 6×6 leading principal block (PD in #340),
the full 7×7 determinant sign, and the physical C2 hermiticity.
It requires no 7×7 PosDef assumption.

Physical Lean theorems now **proved**:
  physicalC2RadialPickMatrix_seven_eventually_posDef
  physicalC2RadialDefectMatrix_seven_eventually_posDef

The second uses the PREEXISTING invertible physical HB amplitude
gauge (congruence), so all complex linear combinations retain their
sign. The global Hilbert/Parseval transport and physical return are
not replaced or simplified away.

## Audit boundary

FOCUSED validation: PASS, Lean 4.32 with -DwarningAsError=true.
#prints report only
  propext, Classical.choice, Quot.sound.
No new axiom, sorry/admit, or merge was introduced.
The independent FULL order-respecting reproduction script was
executed and completed with exit code 0 on 2026-11-17.
Recompiled all historical GoN–CSA comparator modules and the
new seventh-order source, parity, congruence, sign and physical closure
with Lean 4.32 and -DwarningAsError=true.
Result: PASS; only propext, Classical.choice and Quot.sound in
#print axioms; no error, sorryAx or new custom axiom.
This is a reproducible fixed-order proof, not an all-order sign claim.

Reproduce:
  research/projective-chiral-complex-cauchy/validate-physical-seven.sh
    /home/thlinux/carry-self-adjoint-operator

This is a LOCAL result at fixed N=7, for sufficiently large k
on the particular radial grid. It does NOT give arbitrary-position
Schur contractivity, positive Hankels of every order, a global
Gram/Hankel identification, or RH.

N=8 would require a new shifted odd K4 determinant and an
eight-point physical transport. None of that follows from N=7.
