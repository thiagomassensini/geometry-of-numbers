#!/usr/bin/env python3
"""Exact source-coordinate regressions; no moments, zeros or height inputs."""
from fractions import Fraction as Q
from math import comb,factorial,isqrt
from pathlib import Path
import json
Z=(Q(0),Q(0));I=(Q(0),Q(1))
def G(x=0,y=0):return (Q(x),Q(y))
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def sub(x,y):return (x[0]-y[0],x[1]-y[1])
def mul(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def sc(a,x):return (a*x[0],a*x[1])
def cj(x):return (x[0],-x[1])
def pw(x,n):
 r=G(1)
 for _ in range(n):r=mul(r,x)
 return r

def inv(x):
 d=x[0]**2+x[1]**2
 assert d
 return (x[0]/d,-x[1]/d)
def total(xs):
 r=Z
 for x in xs:r=add(r,x)
 return r

def choose(n,m):return Q(comb(n,m)) if m<=n else Q(0)
def stencil(m,r):return Q((-1)**(m-r))*choose(m,r) if r<=m else Q(0)
def newton(kappa,x):
 delta=sc(1/kappa,I);N=len(x)
 return [sc(Q((-1)**(m//2)*factorial(m)),mul(pw(delta,m),
   total(sc(choose(r,m),x[r]) for r in range(N)))) for m in range(N)]
def input_chart(kappa,A,y):
 delta=sc(1/kappa,I);N=len(y)
 return [mul(A[r],total(sc(Q((-1)**(m//2))*stencil(m,r),
  mul(inv(sc(Q(factorial(m)),pw(delta,m))),y[m])) for m in range(N))) for r in range(N)]
def pointwise(x,y):return [mul(z,w) for z,w in zip(x,y)]
def data(N,offset):return [G(Q((-1)**(r+offset)*(r+offset+1),r+2),Q(r+offset,2*r+3)) for r in range(N)]
def cross_inner(kappa,lam,x,y):
 scale=Q(isqrt(int(kappa))*isqrt(int(lam)))
 assert scale**2==kappa*lam
 return total(sc(scale/Q(r+s+2),mul(cj(x[r]),y[s])) for r in range(len(x)) for s in range(len(y)))
def form(kappa,lam,u,v):return sc(Q(1,2),sub(cross_inner(kappa,lam,u[0],v[0]),cross_inner(kappa,lam,u[1],v[1])))
checks=0
sizes=[0,2,4,6,8,10,12,16]
for N in sizes:
 for r in range(N):
  for s in range(N):
   assert sum(stencil(m,r)*choose(s,m) for m in range(N))==Q(r==s);checks+=1
   assert sum(choose(m,r)*stencil(s,m) for m in range(N))==Q(r==s);checks+=1
 for kappa in [Q(1),Q(4),Q(9)]:
  A=data(N,3);q=data(N,5)
  for offset in [0,1,2]:
   x=data(N,offset);y=newton(kappa,x)
   assert input_chart(kappa,A,y)==pointwise(A,x);checks+=1
   # Reverse direction is a finite exact regression, separately from Lean's whole-source theorem.
   assert newton(kappa,input_chart(kappa,[G(1)]*N,x))==x;checks+=1
  x=data(N,0)
  for M in [z for z in sizes if z>=N]:
   extended=x+[Z]*(M-N)
   assert newton(kappa,extended)==newton(kappa,x)+[Z]*(M-N);checks+=1
# Independent cutoffs, radial indices and complex coefficients. Both full legs and all N*M crossings.
for N,M in [(2,4),(4,6),(6,8),(8,12),(12,16)]:
 for kappa,lam in [(Q(1),Q(4)),(Q(4),Q(9)),(Q(9),Q(1))]:
  x=data(N,0);y=data(M,1);A=data(N,3);B=data(M,4);q=data(N,5);p=data(M,6)
  rawx=pointwise(A,x);rawy=pointwise(B,y)
  jetx=input_chart(kappa,A,newton(kappa,x));jety=input_chart(lam,B,newton(lam,y))
  u=(rawx,pointwise(q,rawx));v=(rawy,pointwise(p,rawy))
  ju=(jetx,pointwise(q,jetx));jv=(jety,pointwise(p,jety))
  assert ju==u and jv==v;checks+=2
  assert form(kappa,lam,ju,jv)==form(kappa,lam,u,v);checks+=1
# Existing critical four-source chart, with its actual coefficient formula and phase.
for kappa in [Q(1),Q(4),Q(9),Q(16),Q(100)]:
 for a in [Q(0),Q(1),Q(-3),Q(2,7),-kappa*kappa/7]:
  x=[sc(kappa/Q(6),G(0,z)) for z in [-kappa*kappa-6*a,3*kappa*kappa+6*a,-3*kappa*kappa,kappa*kappa]]
  expected=[Z,G(-a),Z,G(-1)]
  assert newton(kappa,x)==expected;checks+=1
  assert newton(kappa,x)!=[sc(-1,z) for z in expected];checks+=1
record={'PASS':True,'exact_gaussian_fraction_checks':checks,
 'tested_dimensions':sizes,'canonical_moments_used':False,'zero_or_height_inputs':False,
 'both_binomial_matrix_inverses_checked':True,'both_native_chart_directions_tested':True,
 'prefix_coherence_and_zero_extension':True,'independent_complex_arguments_and_radial_indices':True,
 'full_two_legs_and_all_cauchy_crossings':True,'wrong_global_phase_detected':True,
 'amplitudes_and_return_samples_scope':'generic algebra identity regressions only; not evaluations of the native completed functions or positivity evidence',
 'lean_scope':'all finite n is proved in Lean; these finite rational cases are regressions only'}
r=Path(__file__).resolve().parent/'evidence';r.mkdir(exist_ok=True)
(r/'mechanism-probe.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
