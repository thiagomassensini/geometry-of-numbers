# Physical C2 radial Cauchy–Pick 8×8 — the odd-source sign mechanism

Date: 2026-11-17
Branch: task/gon-c2-pick-eight-schur-20261117
Base: GoN #341, commit fbc86ab; stacked over #340/#339/#338/#337/#336/#335/#334.
No merge, no change to the original CSA or historical PR branches.

## Source-first genealogy

Original centered bracket C2 and material centres/legs/seed/depth
→ full physical Green return and L¹/L² gradients → TFVD/Parseval
→ camera → archimedean completion → complex native germ
→ projective-chiral Cauchy–Pick → original Hermite–Biehler quotient.

The bracket, Genuine synthesis and completed F are distinct.
The physical Pick is NOT redefined as a canonical moment Hankel
or as the Gram of finite-dimensional scalar-readout vectors.
Original source sign certificates are inputs only after the complex
source-to-native equality and exact binomial transport.

## Main NEW result: original 8-coordinate odd-source sign

CSA defines
  a_j = nativeSourceOddBoundaryCoefficient j = 2 h_j,
where h_j is the canonical completed-native log-derivative moment.
This equality follows from the original native prime-depth recurrence.

The eight-coordinate odd physical boundary energy is the *original*
CSA expression with ALL six crosses:
  Q(u,v,w,t)
   = a1|u|²+a3|v|²+a5|w|²+a7|t|²
    -2a2 Re(conj(u)v)+2a3 Re(conj(u)w)-2a4 Re(conj(u)t)
    -2a4 Re(conj(v)w)+2a5 Re(conj(v)t)
    -2a6 Re(conj(w)t).

The alternating signs are a diagonal congruence with
diag(1,-1,1,-1) of the native real Hankel matrix (a_(i+j+1)).
This is a structural fact, not a newly chosen metric.

CSA had already proved the complete-square identity:
  Q(u,v,w,t) = Q3(u+(C0/delta6)t,v+(C1/delta6)t,
                  w+(C2/delta6)t) + (delta8/delta6)|t|².
Here delta6= nativeSourceSixOddDiscriminant >0 and
delta8 = nativeSourceEightOddDiscriminant, with ALL old/new crosses.

NEW exact Lean proof in PhysicalPickEightDiscriminantBridge.lean:
  nativeSourceEightOddDiscriminant_eq_nativeHankel_four_det
      delta8 = det [a_(i+j+1)] for i,j=0..3.
  nativeSourceEightOddDiscriminant_eq_sixteen_shiftedHankel_four_det
      delta8 = 16 det K4, K4=[h_(i+j+1)] for i,j=0..3.
The factor 16 is exactly 2^4 from a_j=2h_j.

From GoN #340, delta6=8 det K3. NEW:
  nativeSourceEightOddMargin_eq_two_shiftedHankel_ratio
      delta8/delta6 = 2 det K4 / det K3.
This is the exact fourth-coordinate Schur residual in the original
CSA norm, NOT a sign inferred from an isolated diagonal.

The independent original GoN source theorem
  CarryCriticalSource.sourceMatrices_through_four_posDef 1 4
already certified the source K4 > 0, from the unchanged finite
physical source and theta sign. We formally proved equality
to the canonical shifted Hankel 4×4:
  canonicalCompletedNativeShiftedHankel_four_posDef
  canonicalCompletedNativeShiftedHankel_four_det_pos.

Consequently the following are now Lean-proved, without new sign
premises or target Gram:
  nativeSourceEightOddDiscriminant_pos
  nativeSourceEightOddMargin_pos
  nativeSourceEightOddBoundaryEnergy_strict_pos
(the last for every nonzero COMPLEX vector u,v,w,t).

There is also a direct positive answer to the original CSA
characteristic ceiling gate:
  nativeSourceEightCharacteristicCoefficient_lt_ceiling
     completedNativeRealEvenCharacteristicCoefficient 8
       < nativeSourceEightCharacteristicCeiling.
This is obtained via the original CSA iff and the proved delta8>0,
not by altering the characteristic factor or making a new assumption.
It is a fixed-order source-8 strict bound, not all-order.

## Physical 8×8 Pick and HB defect

The eight canonical radial sample heights are exactly
  z_j=i(j+1)/(k+1),  j=0,1,2,3,4,5,6,7.

The 8×8 confluent coefficient matrix C has entries
  C_(p,q) = h_((p+q)/2) if p+q is even, 0 otherwise.
A true simultaneous parity permutation [0,2,4,6;1,3,5,7]
is formalized in c2_eight_parity_determinant and gives
  det C8 = det H4 * det K4.
H4 is from the preexisting material Cholesky4 H4=T4*T4ᵀ,
det T4>0; K4 is source-positive as above.

The analytic native two-step radial limit (already all-order in CSA)
gives a strictly positive confluent determinant for sufficiently large
k, now proved for N=8.

The all-N binomial congruence ALREADY existed in CSA:
  completedGreenComplexShiftedKernelForwardDifferenceMatrix_apply
  completedGreenComplexForwardDifferenceTransform
  completedGreenComplexForwardDifferenceCoefficient.
We reuse the exact formula
  T_N(h)_(i,p)=(-1)^(p-i)choose(p,i)/(p!h^p) for i<=p.
NEW specialization in PhysicalPickEightCongruence.lean proves,
for ANY complex kernel and ALL 64 crosses:
  D8 = T8ᴴ K8 T8.
No artificial isometry, no deleted crosses, no need to expand 64
separate polynomial goals. The determinant transport is exact:
  det D8 = normSq(det T8) * det K8.
The sign returns to the ORIGINAL native dslope Pick.

The genuine C2 material Pick equals the native complex-germ sample
matrix for the fixed eight-point radial family by the previous
source-first GoN #335 theorem. Hermiticity comes from the physical
divided response, not assumed PSD. Its TRUE leading principal 7×7
is strictly PosDef by GoN #341.

NEW Schur 7+1 generic theorem:
  hermitian_fin_eight_posDef_of_leading_posDef_det_pos
combines Hermiticity, leading 7×7 PD and determinant > 0.
The physical HB gauge is invertible, transporting strictness.

NEW final Lean theorems:
  physicalC2RadialPickMatrix_eight_eventually_posDef
  physicalC2RadialDefectMatrix_eight_eventually_posDef.

## Scope / validation

Lean 4.32, -DwarningAsError=true; focused compilation of all NEW
source-discriminant, parity, congruence and physical theorems PASS.
Axioms only: propext, Classical.choice, Quot.sound. No sorry/admit,
no custom axiom, no merge, no new shared Lake dependency.

Full ordered audit:
  research/projective-chiral-complex-cauchy/validate-physical-eight.sh
  /home/thlinux/carry-self-adjoint-operator

Scope is LOCAL, radial, fixed N=8, eventually in k without explicit
numerical threshold. Not arbitrary-position Schur contraction,
all-order positive Hankel/Gram or RH.

For N=9 the next newly APPLIED sign is even H5, but its
positive definiteness is ALREADY certified in
  CarryCriticalSource.even_source_five_posDef
under the original source, so no new theta integration is needed.
For fixed N=10, odd K5 is already certified by
  CarryThetaPattern.odd_source_five_posDef.
For N=11, even H6 is already certified by
  CarrySixthEven.even_source_six_posDef.
For N=12, odd K6 is already certified by
  CarrySixthOdd.odd_source_six_posDef.
Each requires an exact canonical identification and the physical
N-point radial sign transport/Schur closure before being claimed.
These are FOUR FINITE source certificates, NOT arbitrary-order
positivity, uniform radial cutoff or an infinite physical Gram.
The binomial finite-difference congruence itself is already
general in N in the original CSA.
