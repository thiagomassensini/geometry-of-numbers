#!/usr/bin/env python3
"""Exact Gaussian-rational Green regressions; no canonical moments or sign input."""
from fractions import Fraction as Q
from math import comb,factorial
from pathlib import Path
import json
Z=(Q(0),Q(0))
def G(x=0,y=0):return (Q(x),Q(y))
def plus(a,b):return (a[0]+b[0],a[1]+b[1])
def minus(a,b):return (a[0]-b[0],a[1]-b[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def cj(a):return (a[0],-a[1])
def scale(t,a):return (t*a[0],t*a[1])
def total(xs):
 r=Z
 for x in xs:r=plus(r,x)
 return r
def D(c,p):return [scale((j+1)**p,x) for j,x in enumerate(c)]
def E(c,p=0):return total(D(c,p))
def K(w,c,d):return total(scale(w[j]/Q(i+j+2),mul(cj(c[i]),d[j])) for i in range(len(c)) for j in range(len(d)))
def flux(m,c,d):return total(scale((-1)**p,mul(cj(E(c,p)),E(d,m-1-p))) for p in range(m))
def sym(w,c,d):return plus(K(w,c,d),K(w,d,c))
v=[G(0,Q(-1,6)),G(0,Q(1,2)),G(0,Q(-1,2)),G(0,Q(1,6))]
def X(a,t):return [plus(scale(t**3+12*a*t,x),scale(a*t,y)) for x,y in zip(v,D(v,2))]
checks=0
c=[G(1,2),G(-3,1),G(2,-1),G(0,1)];d=[G(2,-3),G(1,1),G(-4,2)]
for m in range(13):
 left=minus(K([Q(1)]*len(d),c,D(d,m)),scale((-1)**m,K([Q(1)]*len(d),D(c,m),d)))
 assert left==flux(m,c,d);checks+=1
for t in [Q(1),Q(2),Q(9),Q(23)]:
 for a,b in [(Q(0),Q(0)),(Q(1),Q(1)),(Q(2,7),Q(3,11)),(Q(-3),Q(5))]:
  x,y=X(a,t),X(b,t)
  assert E(x)==Z;checks+=1
  assert E(x,1)==G(0,a*t);checks+=1
  assert E(x,2)==G(0,10*a*t);checks+=1
  assert E(x,3)==G(0,t**3+77*a*t);checks+=1
  expected={1:Q(0),3:-a*b*t**2,5:-(a+b)*t**4-54*a*b*t**2}
  for m,value in expected.items():
   w=[Q((j+1)**m) for j in range(4)]
   assert flux(m,x,y)==sym(w,x,y)==G(value);checks+=1
  for e,vv,q in [(Q(2),Q(-1),Q(3)),(Q(-3),Q(4),Q(-2))]:
   full=[Q(2),Q(-3,2),Q(5,7),Q(11,3)]
   head=[e*(j+1)/t+vv*(j+1)**3/t**3+q*(j+1)**5/t**5 for j in range(4)]
   tail=[w-h for w,h in zip(full,head)]
   value=-vv*a*b-q*(a+b)-54*q*a*b/t**2
   assert scale(t,sym(head,x,y))==G(value);checks+=1
   assert scale(t,sym(full,x,y))==plus(G(value),scale(t,sym(tail,x,y)));checks+=1
x=X(Q(1),Q(1));assert sym([Q((j+1)**5) for j in range(4)],x,x)==G(-56);checks+=1
# At kappa=2*r^2 the ORIGINAL square-root chiral amplitudes are Gaussian rational.
def vpl(c,d):return [plus(x,y) for x,y in zip(c,d)]
def vmi(c,d):return [minus(x,y) for x,y in zip(c,d)]
def B(u,v):return scale(Q(1,2),minus(K([Q(1)]*len(v[0]),u[0],v[0]),K([Q(1)]*len(v[1]),u[1],v[1])))
def state(w,x,r):
 contrast=[mul(G(0,r),z) for z in x]
 mean=[mul(G(0,2*r),scale(ww,z)) for ww,z in zip(w,x)]
 return vpl(contrast,mean),vmi(mean,contrast)
def tailstate(w,x,r):
 z=[mul(G(0,2*r),scale(ww,zz)) for ww,zz in zip(w,x)]
 return z,z
for rr in [1,2,3]:
 t=Q(2*rr*rr)
 for a,b in [(Q(1),Q(1)),(Q(2,7),Q(-3,11)),(Q(0),Q(2))]:
  x,y=X(a,t),X(b,t);e,vv,q=Q(2),Q(-1),Q(3)
  full=[Q(2),Q(-3,2),Q(5,7),Q(11,3)]
  head=[e*(j+1)/t+vv*(j+1)**3/t**3+q*(j+1)**5/t**5 for j in range(4)]
  tail=[w-h for w,h in zip(full,head)]
  u,z=state(full,x,rr),state(full,y,rr);eu,ez=tailstate(tail,x,rr),tailstate(tail,y,rr)
  hu=(vmi(u[0],eu[0]),vmi(u[1],eu[1]));hz=(vmi(z[0],ez[0]),vmi(z[1],ez[1]))
  assert B(eu,ez)==Z;checks+=1
  assert plus(B(u,ez),B(eu,z))==scale(t,sym(tail,x,y));checks+=1
  assert B(hu,hz)==G(-vv*a*b-q*(a+b)-54*q*a*b/t**2);checks+=1
  assert B(u,z)==plus(B(hu,hz),plus(B(hu,ez),B(eu,hz)));checks+=1
  assert vmi(hu[0],hu[1])==vmi(u[0],u[1]);checks+=1
record={'PASS':True,'exact_gaussian_fraction_checks':checks,'both_complex_quadratures':True,'canonical_moments_used':False,'scope':'finite regression of original source algebra; negative monomial layer is not a negative full-native response'}
p=Path(__file__).resolve().parent/'evidence/mechanism-probe.json';p.parent.mkdir(exist_ok=True);p.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
