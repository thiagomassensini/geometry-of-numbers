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

def response(t): return C(1+t*t,t/2)
def forcing(t): return C(1+t/3,t*t/7)
a=F(3,5)
w=C(2,1)
mass=normsq(w)
def residual(t,u): return C(t*u*(1-3*t*u))
def completed(t,u):
    return mul(C(2*a*a*t*u),mul(mul(conj(response(t)),response(u)),residual(t,u)))
def remainder(t,u):
    return add(completed(t,u),mul(C(a*mass),mul(conj(forcing(t)),forcing(u))))
def center(c,t):
    return [div(neg(total(mul(ci,forcing(ti)) for ci,ti in zip(c,t))),forcing(F(0)))]+c
checks=[]
for N,M in [(1,1),(2,3),(4,2),(3,5)]:
    t=[F(i+1,10) for i in range(N)]
    u=[F(j+1,11) for j in range(M)]
    c=[C(F(i+1,i+2),F(1,i+3)) for i in range(N)]
    d=[C(F(j+2,j+3),F(-1,j+4)) for j in range(M)]
    for normalized in [False,True]:
        cc=[div(ci,mul(C(ti),response(ti))) for ci,ti in zip(c,t)] if normalized else c
        dd=[div(di,mul(C(ui),response(ui))) for di,ui in zip(d,u)] if normalized else d
        tc,ud=[F(0)]+t,[F(0)]+u
        chat,dhat=center(cc,t),center(dd,u)
        assert total(mul(ci,forcing(ti)) for ci,ti in zip(chat,tc))==C()
        assert total(mul(di,forcing(ui)) for di,ui in zip(dhat,ud))==C()
        lhs=form([[remainder(ti,ui) for ui in ud] for ti in tc],chat,dhat)
        rhs=form([[completed(ti,ui) for ui in u] for ti in t],cc,dd)
        assert lhs==rhs
        if normalized:
            assert lhs==mul(C(2*a*a),form([[residual(ti,ui) for ui in u] for ti in t],c,d))
        checks.append({'N':N,'M':M,'regular_input':normalized})
for t in [F(1,10),F(-1,5),F(2,7)]:
    f0,ft=forcing(F(0)),forcing(t)
    v0,vt=mul(f0,w),mul(ft,w)
    reduced_t=(vt,mul(C(a*t),vt))
    reduced_0=(v0,C())
    ratio=div(ft,f0)
    pair=(sub(reduced_t[0],mul(ratio,reduced_0[0])),
          sub(reduced_t[1],mul(ratio,reduced_0[1])))
    assert pair==(C(),mul(C(a*t),vt)) and normsq(pair[1])>0
    green=sub(mul(conj(pair[1]),pair[0]),mul(conj(pair[0]),pair[1]))
    cross=sub(mul(conj(pair[1]),reduced_0[0]),mul(conj(pair[0]),reduced_0[1]))
    assert green==C() and normsq(cross)>0
    assert div(cross,C(t))==mul(C(a),mul(conj(vt),v0))
result={'status':'PASS','arithmetic':'Fraction in both complex components',
        'provenance':'Synthetic controls only; no canonical moment or zero inputs.',
        'polarized_families':checks,'retained_leg_cases':3}
out=Path(__file__).resolve().parent/'evidence'
out.mkdir(exist_ok=True)
(out/'exact-controls.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 8 rectangular complex families and 3 nonzero retained-leg controls')
