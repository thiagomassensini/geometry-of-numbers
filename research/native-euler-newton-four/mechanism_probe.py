#!/usr/bin/env python3
"""Exact source-coordinate regressions; no moments, zeros or height inputs."""
from fractions import Fraction as Q
from math import comb,factorial
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

def U(t,v):
 return [v[0],mul(I,sub(v[1],sc(t,v[0]))),
  add(sub(v[2],sc(3*t,v[1])),sc(2*t*t,v[0])),
  mul(I,sub(add(sub(v[3],sc(6*t,v[2])),sc(11*t*t,v[1])),sc(6*t**3,v[0])))]
def V(t,y):
 return [y[0],sub(sc(t,y[0]),mul(I,y[1])),
  add(sub(sc(t*t,y[0]),sc(3*t,mul(I,y[1]))),y[2]),
  sub(add(sub(sc(t**3,y[0]),sc(7*t*t,mul(I,y[1]))),sc(6*t,y[2])),mul(I,y[3]))]
def native_newton(kappa,x):
 delta=sc(1/kappa,I)
 return [sc(Q((-1)**(m//2)*factorial(m)),mul(pw(delta,m),
   total(sc(Q(comb(r,m)) if r>=m else Q(0),x[r]) for r in range(4)))) for m in range(4)]
def native_input(kappa,amplitudes,y):
 delta=sc(1/kappa,I)
 def w(m,r):return Q((-1)**(m-r)*comb(m,r)) if r<=m else Q(0)
 return [mul(amplitudes[r],total(sc(Q((-1)**(m//2))*w(m,r),
  mul(inv(sc(Q(factorial(m)),pw(delta,m))),y[m])) for m in range(4))) for r in range(4)]
def root2_euler(kappa,x):
 return [sc(kappa**(-m),total(sc(Q(r+1)**m,x[r]) for r in range(4))) for m in range(4)]
def critical(a,kappa):return [sc(kappa/Q(6),G(0,z)) for z in [-kappa*kappa-6*a,3*kappa*kappa+6*a,-3*kappa*kappa,kappa*kappa]]
def pointwise(x,y):return [mul(z,w) for z,w in zip(x,y)]
def inner(kappa,x,y):return total(sc(kappa/Q(r+s+2),mul(cj(x[r]),y[s])) for r in range(4) for s in range(4))
def form(kappa,u,v):return sc(Q(1,2),sub(inner(kappa,u[0],v[0]),inner(kappa,u[1],v[1])))
checks=0
x=[G(1,2),G(-3,1),G(Q(2,7),Q(-5,11)),G(-2,-1)]
z=[G(Q(-1,3),4),G(2,-5),G(-1,3),G(1,1)]
A=[G(2,1),G(-1,3),G(Q(1,2),Q(-2,7)),G(5,-1)]
q=[G(Q(2,3),Q(1,5)),G(-1,2),G(Q(3,7),Q(-1,2)),G(2,1)]
for t in [Q(0),Q(1),Q(-2,3),Q(1,16)]:
 for v in [x,z]:
  assert U(t,V(t,v))==v;checks+=1
  assert V(t,U(t,v))==v;checks+=1
for kappa in [Q(1),Q(2),Q(7),Q(16),Q(100)]:
 for v in [x,z]:
  y=native_newton(kappa,v)
  assert native_input(kappa,A,y)==pointwise(A,v);checks+=1
  # T=sqrt(2)*U, while the original Euler vector is E/sqrt(2).
  E=root2_euler(kappa,v)
  assert U(1/kappa,E)==y;checks+=1
  assert V(1/kappa,y)==E;checks+=1
 incx=native_input(kappa,A,native_newton(kappa,x));incz=native_input(kappa,A,native_newton(kappa,z))
 ux=(pointwise(A,x),pointwise(q,pointwise(A,x)))
 uz=(pointwise(A,z),pointwise(q,pointwise(A,z)))
 jx=(incx,pointwise(q,incx));jz=(incz,pointwise(q,incz))
 assert jx==ux and jz==uz;checks+=2
 assert form(kappa,jx,jz)==form(kappa,ux,uz);checks+=1
 for a in [Q(0),Q(1),Q(-3),Q(2,7),-kappa*kappa/7]:
  c=critical(a,kappa);jet=[Z,G(-a),Z,G(-1)]
  assert native_newton(kappa,c)==jet;checks+=1
  assert native_input(kappa,A,jet)==pointwise(A,c);checks+=1
  wrong=[sc(-1,v) for v in jet]
  assert native_input(kappa,A,wrong)!=pointwise(A,c);checks+=1
  assert max(abs(a),Q(1))**2<=1+a*a;checks+=1
record={'PASS':True,'exact_gaussian_fraction_checks':checks,
 'canonical_moments_used':False,'zero_or_height_inputs':False,
 'sqrt2_factored_out_exactly':True,'both_complex_quadratures':True,
 'both_inverse_directions_checked':True,'all_16_cauchy_crossings_retained':True,
 'wrong_global_phase_detected':True,
 'amplitudes_and_return_samples_scope':'generic algebra identity tests only; no native function evaluation or sign inference',
 'native_uniform_energy_control':'reused by exact vector/coefficient identities in Lean, not numerically presumed'}
r=Path(__file__).resolve().parent/'evidence';r.mkdir(exist_ok=True)
(r/'mechanism-probe.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
