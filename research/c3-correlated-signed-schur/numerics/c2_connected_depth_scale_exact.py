#!/usr/bin/env python3
"""Reproduce exact rational C2 connected-defect / Schur obstruction.

The formulas are already formally proved by Lean for the dyadic tower
T=60*2^k. The wider scan is EVIDENCE, not a theorem for all cutoffs.
No zeros, moment sequence or eigenvalues are input.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from json import dumps

def branch_mass(T, m, plus):
    assert m>0
    # branch point 2**depth*m +/-1 <= T.
    numer=T-1 if plus else T+1
    K=(numer//m).bit_length()-1
    return F(0) if K<2 else F(1,2)-F(1,2**K)

def mass(T,m):
    return branch_mass(T,m,False)+branch_mass(T,m,True)

def defect(T,p,q):
    return mass(T,p)*mass(T,q)-mass(T,p*q)

rows=[]
for k in range(13):
    T=60*2**k
    d=defect(T,3,5)
    K33=defect(T,3,3)
    K55=defect(T,5,5)
    det=K33*K55-d**2
    assert d==F(3,8)*F(1,2**k)+F(1,32)*F(1,4**k)
    assert det==-F(1,64*4**k)
    assert 2**k*d==F(3,8)+F(1,32*2**k)
    assert (2**k)**2*det==-F(1,64)
    rows.append(dict(k=k,cutoff=T,m3=str(mass(T,3)),
                     m5=str(mass(T,5)),m9=str(mass(T,9)),
                     m15=str(mass(T,15)),m25=str(mass(T,25)),
                     positive_connected_defect=str(d),
                     kernel_det=str(det),normalized_defect=str((2**k)*d),
                     normalized_kernel_det=str((2**k)**2*det),
                     rank_one_repair_threshold_exact=str(F(1)/(F(16)+F(1,2**k)))))
print("Verified 13 exact-rational dyadic levels; det scaled = -1/64")

# Check the exact doubling conjecture through a deliberately finite box:
dup_checked=0
for T in range(1250):
    for m in range(1,170):
        assert mass(T,2*m)==max(F(0),2*mass(T,m)-1)
        dup_checked+=1
print("Finite doubling scan, checked",dup_checked,"(NOT universal proof)")

# Only check transitions where any source mass changes;
# all masses are step functions in the integer cutoff.
pair_checked=0; transition_checked=0; negatives=0; zeros=0
for p,q in product(range(2,52),repeat=2):
    ts={0}
    for m in (p,q,p*q):
        for k in range(2,18):
            for s in (-1,1):
                T=2**k*m+s
                if T<=250000:ts.add(T)
    for T in ts:
        cur=mass(T,p*q)-mass(T,p)*mass(T,q)
        assert cur<=0,(p,q,T,cur)
        transition_checked+=1
        if cur<0:negatives+=1
        else:zeros+=1
    pair_checked+=1
print("2500-pair transition scan, checked",transition_checked,
      "negative",negatives,"zero",zeros,"(NOT universal proof)")

out=Path(__file__).resolve().parent.parent/"evidence"/"c2_connected_depth_scale_exact.json"
out.write_text(dumps(dict(
    status="FORMAL_LEAN_DYADIC_TOWER_PLUS_FINITE_EXACT_RATIONAL_SWEEPS",
    direct_input="original oddCoreTruncatedMass: k>=2, both legs 2^k*m +/-1, weight 2^-k",
    no_zero_list_or_native_moment_input=True,
    lean_all_k_proven="T=60*2^k, connected(3,5) <0, b_T(15)<0, normalized naive 2x2 det=-1/64, exact hypothetical rank-one compensation",
    empirical_not_lean_general=dict(duplication_T_range="[0,1249]",
        duplication_m_range="[1,169]",duplication_checked=dup_checked,
        product_pair_range="[2,51] x [2,51]",pair_checked=pair_checked,
        transition_checked=transition_checked,negative_cases=negatives,
        zero_cases=zeros,positive_cases=0,
        statement="No violation of a_T(pq)<=a_T(p)*a_T(q) in this finite scan"),
    cutoff_rows=rows,
    caution="Kernel built from negative connected C2 mass is NOT the native F(z) moment Gram. PSD of the completed source remains open."
    ),indent=2)+"\n")
print("EVIDENCE",out)
