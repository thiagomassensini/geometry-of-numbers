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

# Synthetic controls only: both original Green orientations and true
# divided-difference diagonal values, followed by finite complex families.
a=F(3,5); slope=F(4,5); mu=F(-2,7); w=C(2,1)
def forcing(t): return C(1+t/3,t*t/7)
def chi(t): return C(slope*t,mu*t*t)
def dchi(t): return C(slope,2*mu*t)
def ds(t,u): return dchi(t) if t==u else div(sub(chi(u),chi(t)),C(u-t))
def cp(t): return C(t+t*t,t*t/3),div(neg(mul(forcing(t),chi(t))),conj(w))
def fp(t): return mul(forcing(t),w),C()
def reduce(t,x): return sub(x[0],mul(C(a*t),x[1])),mul(C(a*t),x[0])
def green(x,y): return sub(mul(conj(x[1]),y[0]),mul(conj(x[0]),y[1]))
def mixed(t,u): return add(green(reduce(t,cp(t)),reduce(u,fp(u))),green(reduce(t,fp(t)),reduce(u,cp(u))))
def eta(t): return mul(conj(w),cp(t)[0])
def companion(t,u): return mul(C(-a),add(mul(conj(forcing(t)),eta(u)),mul(conj(eta(t)),forcing(u))))
def weight(t,u): return mul(C(a*a*t*u),mul(conj(forcing(t)),forcing(u)))
def pole(t,u): return mul(weight(t,u),sub(chi(t),conj(chi(t))))
def retained(t,u): return mul(weight(t,u),ds(t,u))
def completed(t,u): return C(t*u*(1+t*u),t*u*(u-t))
def remainder(t,u): return add(completed(t,u),mul(C(a*normsq(w)),mul(conj(forcing(t)),forcing(u))))
def compensated(t,u): return sub(sub(remainder(t,u),companion(t,u)),retained(t,u))
def center(c,t): return [div(neg(total(mul(ci,forcing(ti)) for ci,ti in zip(c,t))),forcing(F(0)))]+c
nodes=[F(0),F(1,10),F(-1,5),F(2,7)]
for t in nodes:
 for u in nodes:
    assert mixed(t,u)==add(mul(C(u-t),add(companion(t,u),retained(t,u))),pole(t,u))
    assert mul(C(u-t),ds(t,u))==sub(chi(u),chi(t))
    if t==u and t:
        assert pole(t,t)!=C()
        assert div(pole(t,t),C(t**4))==mul(C(a*a),mul(mul(conj(forcing(t)),forcing(t)),C(0,2*mu)))
checks=[]
for N,M in [(1,1),(2,3),(4,2),(3,5)]:
    t=[F(i+1,10) for i in range(N)];u=[F(j+1,11) for j in range(M)]
    c=[C(F(i+1,i+2),F(1,i+3)) for i in range(N)]
    d=[C(F(j+2,j+3),F(-1,j+4)) for j in range(M)]
    tc,uc=[F(0)]+t,[F(0)]+u;chat,dhat=center(c,t),center(d,u)
    left=add(form([[retained(ti,uj) for uj in u] for ti in t],c,d),
             form([[compensated(ti,uj) for uj in uc] for ti in tc],chat,dhat))
    right=form([[completed(ti,uj) for uj in u] for ti in t],c,d)
    assert left==right
    checks.append({'N':N,'M':M,'same_source_centering':True})
result={'status':'PASS','arithmetic':'Fraction in both complex components',
        'provenance':'Synthetic controls, distinct from the native source and numerical canary.',
        'two_parameter_nodes':len(nodes)**2,'includes_diagonal':True,
        'nonzero_diagonal_phase_cases':len(nodes)-1,'rectangular_families':checks,
        'no_native_sign_claim':True}
out=Path(__file__).resolve().parent/'evidence';out.mkdir(exist_ok=True)
(out/'exact-controls.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 16 two-parameter controls with actual confluent derivatives; 4 rectangular centered families')
