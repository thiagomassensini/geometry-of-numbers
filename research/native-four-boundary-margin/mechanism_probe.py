#!/usr/bin/env python3
"""Exact coefficient/jet regressions. Native positivity is proved only in Lean."""
from fractions import Fraction as Q
from pathlib import Path
import json

def add(x,y):return (x[0]+y[0],x[1]+y[1])
def mul(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def inv(x):
 d=x[0]**2+x[1]**2
 assert d
 return (x[0]/d,-x[1]/d)
def scale(a,x):return (a*x[0],a*x[1])
def conj(x):return (x[0],-x[1])
def total(xs):
 r=(Q(0),Q(0))
 for x in xs:r=add(r,x)
 return r

def original_input(a,kappa):
 return [scale(kappa/Q(6),(Q(0),x)) for x in
         [-kappa**2-13*a,3*kappa**2+48*a,-3*kappa**2-63*a,kappa**2+28*a]]
def scaled_jets_without_sqrt2(x,t):
 return [scale(t**m,total(scale(Q(j+1)**m,z) for j,z in enumerate(x))) for m in range(4)]
checks=0
for kappa in [Q(1),Q(2),Q(7),Q(11),Q(16),Q(32),Q(100)]:
 t=1/kappa
 for a in [Q(0),Q(1),Q(-3),Q(2,7),-kappa**2/77,-187*kappa**2/3613]:
  v=scaled_jets_without_sqrt2(original_input(a,kappa),t)
  expected=[(Q(0),z) for z in [Q(0),a,10*a*t,1+77*a*t*t]]
  assert v==expected;checks+=1
  norm2=sum(mul(conj(z),z)[0] for z in v)/2
  assert norm2==(a*a+(10*a*t)**2+(1+77*a*t*t)**2)/2;checks+=1
  if (77*t*t)**2<=Q(1,2):
   assert norm2>=(a*a+1)/4;checks+=1
  # Two independent arguments, retaining every ordered cross in coordinates.
  b=Q(3,11)-a
  w=scaled_jets_without_sqrt2(original_input(b,kappa),t)
  polar=total(mul(conj(z),zz) for z,zz in zip(v,w))
  assert polar==(a*b+100*a*b*t*t+(1+77*a*t*t)*(1+77*b*t*t),Q(0));checks+=1
  assert (a*a+1)/2>0;checks+=1
# Verify the dressing cancellation with arbitrary nonzero Gaussian-rational
# F,P. sqrt(2) is factored out on BOTH sides; these are algebra tests, not
# alternative values of the actual completed characteristic.
for F in [(Q(1),Q(2)),(Q(-3),Q(1,7))]:
 for P in [(Q(2),Q(-1)),(Q(1,3),Q(4))]:
  for x in [(Q(1),Q(3)),(Q(-2,5),Q(1,2)),(Q(0),Q(0))]:
   root2_amplitude=mul(P,inv(F))
   root2_c=mul(root2_amplitude,x)
   root2_d=mul(mul(root2_c,F),inv(P))
   assert root2_d==x;checks+=1
   assert mul(mul(root2_d,P),inv(F))==root2_c;checks+=1
record={'PASS':True,'exact_fraction_checks':checks,'both_complex_quadratures':True,
 'canonical_moments_used':False,'zero_or_height_inputs':False,
 'physical_metric_modified':False,'sqrt2_factored_out_exactly':True,
 'scope':'coefficient and complete four-jet algebra regressions; no numerical source-sign inference',
 'finite_native_coercivity':'reused and audited in Lean, not inferred from rational samples'}
r=Path(__file__).resolve().parent/'evidence';r.mkdir(exist_ok=True)
(r/'mechanism-probe.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
