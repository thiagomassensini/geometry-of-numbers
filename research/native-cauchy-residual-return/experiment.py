#!/usr/bin/env python3
"""Independent exact-rational matrix checks, not a native-source certificate."""
from fractions import Fraction as F
from pathlib import Path
import json

def C(r=0, s=0): return F(r), F(s)
def add(z, w): return z[0]+w[0], z[1]+w[1]
def neg(z): return -z[0], -z[1]
def sub(z, w): return add(z, neg(w))
def mul(z, w): return z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0]
def conj(z): return z[0], -z[1]
def normsq(z): return z[0]**2+z[1]**2
def div(z, w):
    assert normsq(w)
    p=mul(z, conj(w))
    return p[0]/normsq(w), p[1]/normsq(w)
def total(values):
    result=C()
    for value in values: result=add(result,value)
    return result
def form(matrix, c, e):
    return total(mul(mul(conj(c[i]),matrix[i][j]),e[j])
                 for i in range(len(c)) for j in range(len(e)))

families=[]
for k in [0,2,17]:
    for N in range(1,6):
        r=C(F(1,3),F(1,5))
        q=[r]+[C(F(j+2,j+5),F(-j,j+7)) for j in range(1,N+1)]
        deficit=C(1-normsq(r))
        K=[[C(F(k+1,i+j+2)) for j in range(N+1)] for i in range(N+1)]
        B=[[mul(K[i][j],sub(C(1),mul(conj(q[i]),q[j])))
            for j in range(N+1)] for i in range(N+1)]
        a=[mul(C(F(i,i+2)),sub(C(1),mul(conj(r),q[i]))) for i in range(1,N+1)]
        b=[sub(q[i],r) for i in range(1,N+1)]
        reduced=[div(bi,ai) for ai,bi in zip(a,b)]
        residual=[]
        for i in range(1,N+1):
            row=[]
            for j in range(1,N+1):
                projected=sub(K[i][j],div(mul(K[i][0],K[0][j]),K[0][0]))
                assert projected==mul(C(F(i,i+2)*F(j,j+2)),K[i][j])
                schur=sub(B[i][j],div(mul(B[i][0],B[0][j]),B[0][0]))
                physical=mul(K[i][j],sub(mul(conj(a[i-1]),a[j-1]),
                                          mul(conj(b[i-1]),b[j-1])))
                assert physical==mul(deficit,schur)
                feedback_i=sub(C(1),mul(conj(r),q[i]))
                feedback_j=sub(C(1),mul(conj(r),q[j]))
                projected_both=mul(projected,sub(mul(conj(feedback_i),feedback_j),
                                                 mul(conj(b[i-1]),b[j-1])))
                lost=mul(mul(conj(b[i-1]),b[j-1]),
                         div(mul(K[i][0],K[0][j]),K[0][0]))
                assert sub(projected_both,physical)==lost
                assert physical==mul(mul(conj(a[i-1]),a[j-1]),
                    mul(K[i][j],sub(C(1),mul(conj(reduced[i-1]),reduced[j-1]))))
                row.append(physical)
            residual.append(row)
        c=[C(F(i+1,i+2),F((-1)**i,i+3)) for i in range(N)]
        e=[C(F(2*i+1,i+4),F(1,i+5)) for i in range(N)]
        # Independent complex arguments, rather than diagonal norms alone.
        direct=form(residual,c,e)
        S=[[sub(B[i][j],div(mul(B[i][0],B[0][j]),B[0][0]))
            for j in range(1,N+1)] for i in range(1,N+1)]
        assert direct==mul(deficit,form(S,c,e))
        families.append({'k':k,'tail_dimension':N,'matrix_entries':N*N})

# A scalar-strict contraction on every basis vector can expand a combination.
K=[[C(F(1,i+j+4)) for j in range(2)] for i in range(2)]
tau=[C(F(1,2)),C(F(-1,2))]
defect=[[mul(K[i][j],sub(C(1),mul(conj(tau[i]),tau[j])))
         for j in range(2)] for i in range(2)]
assert [normsq(x) for x in tau]==[F(1,4),F(1,4)]
assert defect==[[C(F(3,16)),C(F(1,4))],[C(F(1,4)),C(F(1,8))]]
negative=form(defect,[C(1),C(-1)],[C(1),C(-1)])
assert negative==C(F(-3,16))
# These reduced data can come from genuine scalar-contracting synthetic data.
r=C(F(1,2))
q=[div(add(r,mul(C(F(i,i+2)),tau[i-1])),
       add(C(1),mul(r,mul(C(F(i,i+2)),tau[i-1])))) for i in [1,2]]
assert q==[C(F(8,13)),C(F(2,7))] and all(normsq(x)<1 for x in q)

result={'status':'PASS','arithmetic':'fractions.Fraction in both complex components',
        'provenance':'Synthetic quotient controls; original exact Cauchy kernel. No native moment inputs.',
        'families':families,'matrix_entries_checked':sum(x['matrix_entries'] for x in families),
        'cross_control':{'diagonals':['3/16','1/8'],'cross':'1/4','quadratic':'-3/16',
                         'synthetic_original_return':['1/2','8/13','2/7']}}
out=Path(__file__).resolve().parent/'evidence'
out.mkdir(exist_ok=True)
(out/'exact-controls.json').write_text(json.dumps(result,indent=2)+'\n')
print(f"PASS: {len(families)} rational complex families, {result['matrix_entries_checked']} matrix entries, cross obstruction")
