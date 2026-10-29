#!/usr/bin/env python3
"""Exact finite algebra controls. These are NOT native moment certificates."""
from fractions import Fraction as F
import json

def dot(x,y): return sum((a*b for a,b in zip(x,y)),F(0))
def bracket(eta,x):
    return [F(0)]+[x[n+1]/eta-2*x[n]+eta*x[n-1] for n in range(1,len(x)-1)]+[eta*x[-2]-2*x[-1]]

def trace(eta,x): return x[0],x[1]/eta-x[0]
def returned(eta,x):
    a,b=trace(eta,x)
    return [eta**n*(a+n*b) for n in range(len(x))]

controls=[]
for eta in [F(1,2),F(2,3),F(3,4)]:
    x=[F(int(2<=n<20)) for n in range(23)]
    assert trace(eta,x)==(0,0)
    lhs=dot(x,bracket(eta,x))
    assert lhs==17*(eta+1/eta)-36
    shift=[F(0)]+x[:-1]
    d=[a-b for a,b in zip(shift,x)]
    assert -lhs==(eta+1/eta)/2*dot(d,d)-(eta+1/eta-2)*dot(x,x)
    e0=[F(int(n==0)) for n in range(23)]
    e2=[F(int(n==2)) for n in range(23)]
    assert dot(e2,returned(eta,e0))==-eta**2
    controls.append({'eta':str(eta),'plateau_curvature':str(lhs),'mixed':str(-eta**2)})
assert F(12,17)**2<F(1,2)
print(json.dumps({'status':'PASS','scope':'finite algebra only','controls':controls,
                  'native_lower_square_gap':str(F(1,2)-F(12,17)**2)},indent=2))
