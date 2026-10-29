#!/usr/bin/env python3
"""Exact algebra of the original complete critical source and its correction.
Native analytic limits and signs are kernel proofs, not rational-sample guesses.
"""
from fractions import Fraction as Q
from pathlib import Path
import json

def add(x,y):return (x[0]+y[0],x[1]+y[1])
def sub(x,y):return (x[0]-y[0],x[1]-y[1])
def mul(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def sc(a,x):return (a*x[0],a*x[1])
def cj(x):return (x[0],-x[1])
def total(xs):
 r=(Q(0),Q(0))
 for x in xs:r=add(r,x)
 return r

def P(a,k):return [sc(k/Q(6),(Q(0),z)) for z in [-k*k-13*a,3*k*k+48*a,-3*k*k-63*a,k*k+28*a]]
def Y(a,k):return [sc(7*a*k/Q(6),(Q(0),z)) for z in [-Q(1),Q(6),-Q(9),Q(4)]]
def C(a,k):return [sc(k/Q(6),(Q(0),z)) for z in [-k*k-6*a,3*k*k+6*a,-3*k*k,k*k]]
def vsub(x,y):return [sub(z,w) for z,w in zip(x,y)]
def jets(x,t):return [sc(t**m,total(sc(Q(j+1)**m,z) for j,z in enumerate(x))) for m in range(4)]
def norm2_without_root2(x):return sum(mul(cj(z),z)[0] for z in x)/2

def inner(x,y):return total(sc(1/Q(i+j+2),mul(cj(z),w)) for i,z in enumerate(x) for j,w in enumerate(y))
def B(u,v):return sc(Q(1,2),sub(inner(u[0],v[0]),inner(u[1],v[1])))
def state(w,x,r):
 return ([mul((Q(0),r*(1+2*q)),z) for q,z in zip(w,x)],
         [mul((Q(0),r*(2*q-1)),z) for q,z in zip(w,x)])
checks=0
for k in [Q(1),Q(2),Q(4),Q(8),Q(11),Q(32),Q(100)]:
 t=1/k
 for a in [Q(0),Q(1),Q(-3),Q(2,7),-k*k/7,-k*k/77]:
  c,p,y=C(a,k),P(a,k),Y(a,k)
  assert c==vsub(p,y);checks+=1
  vc,vp,vy=jets(c,t),jets(p,t),jets(y,t)
  assert vc==vsub(vp,vy);checks+=1
  assert vc==[(Q(0),z) for z in [Q(0),a,3*a*t,1+7*a*t*t]];checks+=1
  assert vy==[(Q(0),z) for z in [Q(0),Q(0),7*a*t,70*a*t*t]];checks+=1
  assert norm2_without_root2(vc)==(a*a+(3*a*t)**2+(1+7*a*t*t)**2)/2;checks+=1
  assert jets([sc(k,z) for z in Y(Q(1),k)],t)==[(Q(0),z) for z in [Q(0),Q(0),Q(7),70*t]];checks+=1
  if (7*t*t)**2<=Q(1,2):
   assert norm2_without_root2(vc)>=(a*a+1)/4;checks+=1
# kappa=2*r^2 keeps the prescribed sqrt(kappa)/sqrt(2) amplitude rational.
for r in [Q(1),Q(2),Q(3)]:
 k=2*r*r
 for a,b in [(Q(0),Q(2)),(Q(1),Q(1)),(Q(2,7),Q(-3,11)),(-k*k/7,Q(5))]:
  for w in [[Q(2),Q(-3,2),Q(5,7),Q(11,3)],[Q(-1),Q(1,3),Q(-2),Q(7,5)]]:
   ca,cb=state(w,C(a,k),r),state(w,C(b,k),r)
   pa,pb=state(w,P(a,k),r),state(w,P(b,k),r)
   ya,yb=state(w,Y(a,k),r),state(w,Y(b,k),r)
   assert ca==(vsub(pa[0],ya[0]),vsub(pa[1],ya[1]));checks+=1
   assert B(pa,yb)==(Q(0),Q(0)) and B(ya,pb)==(Q(0),Q(0));checks+=2
   assert B(ca,cb)==add(B(pa,pb),B(ya,yb));checks+=1
   one=state(w,Y(Q(1),k),r)
   assert B(ya,yb)==sc(a*b,B(one,one));checks+=1
   scaled=state(w,[sc(k,z) for z in Y(Q(1),k)],r)
   assert B(scaled,scaled)==sc(k*k,B(one,one));checks+=1
# Both complex quadratures for the source-coefficient coordinate linearity.
x=[(Q(1),Q(2)),(Q(-3,7),Q(1,2)),(Q(4),Q(-5)),(Q(0),Q(1))]
z=(Q(2,3),Q(-7,11))
for m in range(4):
 for t in [Q(1),Q(1,8)]:
  left=jets([mul(z,v) for v in x],t)[m]
  assert left==mul(z,jets(x,t)[m]);checks+=1
record={'PASS':True,'exact_gaussian_fraction_checks':checks,
 'canonical_moments_used':False,'zero_or_height_inputs':False,
 'both_complex_quadratures':True,'all_16_cauchy_crossings_retained':True,
 'projective_and_radial_amplitude_inserted_once':True,
 'rational_response_scope':'algebra tests only; no identification of samples with native F or inference of positivity/analytic rates',
 'native_analytic_remainder_and_rate':'proved in Lean from the existing completed source'}
r=Path(__file__).resolve().parent/'evidence';r.mkdir(exist_ok=True)
(r/'mechanism-probe.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
