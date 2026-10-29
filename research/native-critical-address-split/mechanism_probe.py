#!/usr/bin/env python3
"""Exact rational regression of the literal stencil split. Not a Lean proof."""
from fractions import Fraction as Q
from math import comb, factorial
import json
from pathlib import Path

def stencil(m):
    return [Q((-1)**(m-j)*comb(m,j),factorial(m)) for j in range(m+1)]
def odd(r):
    # imaginary coefficient after factoring the ORIGINAL i
    return [(-1)**(r+1)*x for x in stencil(2*r+1)]
def D(c,p=1): return [x*(j+1)**p for j,x in enumerate(c)]
def add(c,d): return [x+y for x,y in zip(c,d)]
def scale(t,c): return [t*x for x in c]
def kernel(w,c,d):
    return sum((c[i]*d[j]*w[j]/(i+j+2) for i in range(len(c)) for j in range(len(d))),Q(0))
def sym(w,c,d): return kernel(w,c,d)+kernel(w,d,c)
def third(e,f):
    return -f[0]/(360*e**3)+f[1]/(180*e**3)-f[2]/(280*e**3)+f[3]/(1260*e**3)
checks=0
for r in range(6):
    v=odd(r); n=2*r+1
    for p in range(n):
        assert sum(D(v,p))==0; checks+=1
    assert sum(D(v,n))==(-1)**(r+1); checks+=1
    c=odd(r+1)
    lowered=add(add(D(c,2),scale(-(4*r+7),D(c))),scale((2*r+3)*(2*r+4),c))
    assert lowered==scale(-1,odd(r))+[Q(0),Q(0)]; checks+=1
    w=[Q((-1)**j*(j+3),j+2) for j in range(len(c))]
    assert sym(w,c,D(c))==0 and sym(w,D(c,2),D(c))==0; checks+=2
v=odd(1)
for k in [0,1,4,17]:
    t=Q(k+1);e=1/t**2;u=[e*(j+1)**2 for j in range(4)]
    for a,b in [(Q(0),Q(0)),(Q(1),Q(-2)),(Q(2,7),Q(3,11)),(Q(-4),Q(-3))]:
        X=lambda a:add(scale(t**3+12*a*t,v),scale(a*t,D(v,2)))
        Y=lambda a:scale(7*a*t,D(v))
        C=lambda a:add(scale(t**3,v),scale(-a*t,odd(0)+[Q(0),Q(0)]))
        assert C(a)==add(X(a),scale(-1,Y(a)));checks+=1
        for w in [[Q(j+1,2*j+3) for j in range(4)],[Q(1),Q(-2),Q(3),Q(-5)]]:
            f=[t*w[j]/(j+1) for j in range(4)]
            assert sym(w,X(a),Y(b))==sym(w,Y(a),X(b))==0;checks+=1
            assert sym(w,C(a),C(b))==sym(w,X(a),X(b))+sym(w,Y(a),Y(b));checks+=1
            p=-third(e,[(1+a*(u[j]+12*e))*(1+b*(u[j]+12*e))*f[j] for j in range(4)])
            d=49*a*b*e*third(e,[u[j]*f[j] for j in range(4)])
            assert t*sym(w,X(a),X(b))==p;checks+=1
            assert t*sym(w,Y(a),Y(b))==d;checks+=1
# The endpoint term is real data, not assumed zero for arbitrary sources.
c=[Q(1),Q(2),Q(-1),Q(3)];d=[Q(-2),Q(1),Q(4),Q(1)];w=[Q(2),Q(-3),Q(1),Q(5)]
assert kernel(w,D(c),d)+kernel(w,c,D(d))==sum(c)*sum(x*y for x,y in zip(w,d));checks+=1
result={"PASS":True,"exact_fraction_checks":checks,"input":"original factorial stencils; arbitrary independent rational a,b and weights", "canonical_moments_used":False,"scope":"finite algebraic regression; no native sign or all-order positivity claim"}
p=Path(__file__).resolve().parent/'evidence/mechanism-probe.json';p.parent.mkdir(exist_ok=True);p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
