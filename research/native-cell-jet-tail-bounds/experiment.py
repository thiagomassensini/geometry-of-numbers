#!/usr/bin/env python3
"""Finite source regressions and exact synthetic controls. Not native sign proofs."""
from fractions import Fraction as Q
import json
from pathlib import Path
import mpmath as mp
mp.mp.dps=60

def delta2(f,a): return f(a+2)-2*f(a+1)+f(a)
def delta4(f,a): return f(a+4)-4*f(a+3)+6*f(a+2)-4*f(a+1)+f(a)
def boundary(f,a): return (3*f(a+2)-8*f(a+1)+5*f(a))/8
def remainder(f,a): return Q(3,8)*delta4(f,a)+Q(1,2)*delta4(f,a+1)+Q(3,8)*delta4(f,a+2)
accel=0
for f in [lambda n:Q(n**5+1,n+2),lambda n:Q(n**3-2*n+7),lambda n:Q(1,n+1)]:
 for a in [0,3,11]:
  for N in [0,1,2,7]:
   assert sum((delta2(f,a+4*k) for k in range(N)),Q()) == boundary(f,a)-boundary(f,a+4*N)+sum((remainder(f,a+4*k) for k in range(N)),Q())
   accel+=1
for M in [1,2,4,16,1024]:
 for N in [0,1,2,64]:
  lhs=sum((Q(1,(4*(k+M)+3)**2) for k in range(N)),Q())
  rhs=Q(1,4*(4*M-1))-Q(1,4*(4*(N+M)-1))
  assert lhs<=rhs
# These are literal native normalized material sample jets, not moments.
def sample_jet(m,n):
 return mp.power(n,mp.mpf('-0.5'))*(-1j*mp.log(n))**m/mp.factorial(m)
cell_checks=0
clock_checks=0
max_ratio=mp.mpf('0')
for m in range(7):
 for k in [0,1,2,7,31,127,511]:
  a=4*k+3
  value=delta2(lambda n:sample_jet(m,n),a)
  bound=mp.mpf(2)**(m+1)/(a*a)
  assert abs(value)<=bound*(1+mp.mpf('1e-45'))
  clock=delta2(lambda n:mp.log(n)*sample_jet(m,n),a)
  relation=1j*(m+1)*delta2(lambda n:sample_jet(m+1,n),a)
  assert abs(clock-relation)<mp.mpf('1e-45')
  clock_bound=mp.mpf(m+1)*2**(m+2)/(a*a)
  assert abs(clock)<=clock_bound*(1+mp.mpf('1e-45'))
  max_ratio=max(max_ratio,abs(value)/bound)
  cell_checks+=1; clock_checks+=1
# Native finite tail windows are checked without supplying beta's infinite sum.
windows=[]
for m in [0,1,3,5,6]:
 M,N=16,128
 value=sum((delta2(lambda n:sample_jet(m,n),4*(k+M)+3) for k in range(N)),0j)
 bound=mp.mpf(2)**(m+1)/(4*(4*M-1))
 assert abs(value)<=bound
 windows.append({'order':m,'M':M,'N':N,'finite_window_norm':mp.nstr(abs(value),22),'infinite_tail_envelope':mp.nstr(bound,22)})
# The accelerated identity is checked on the SAME native jet samples.
accelerated=[]
for m in [0,1,3,5,6]:
 M,N=16,128
 f=lambda n:sample_jet(m,n)
 a=4*M+3
 d=sum((delta2(f,a+4*k) for k in range(N)),0j)
 rem=lambda n:mp.mpf(3)/8*delta4(f,n)+mp.mpf(1)/2*delta4(f,n+1)+mp.mpf(3)/8*delta4(f,n+2)
 rs=sum((rem(a+4*k) for k in range(N)),0j)
 e=boundary(f,a)-boundary(f,a+4*N)+rs
 assert abs(d-e)<mp.mpf('1e-45')
 accelerated.append({'order':m,'M':M,'N':N,'remainder_window_norm':mp.nstr(abs(rs),22),
  'source_window_norm':mp.nstr(abs(d),22),'scope':'finite native window; both endpoints retained'})
# Algebraic critical readout works for negative and zero pivots too.
controls=[]
for h2 in [Q(0),Q(1),Q(2)]:
 h=[Q(1),Q(1),h2]
 a=[Q(-1),Q(1)]
 pivot=h2-1
 observed=[h[0]+Q(1,101),h[1]-Q(1,103),h[2]+Q(1,107)]
 error=[abs(h[i]-observed[i]) for i in range(3)]
 obs=sum(a[i]*a[j]*observed[i+j] for i in range(2) for j in range(2))
 budget=sum(abs(a[i])*abs(a[j])*error[i+j] for i in range(2) for j in range(2))
 assert abs(pivot-obs)<=budget
 controls.append({'pivot':str(pivot),'observed':str(obs),'budget':str(budget)})
# Costs below refer ONLY to the raw ordinary jet, not to a pivot budget.
costs=[]
for eps in [Q(1,10**8),Q(1,10**25)]:
 m=5
 required=(Q(2)**(m+1)/eps+4)/16
 M=max(1,-(-required.numerator//required.denominator))
 costs.append({'raw_ordinary_jet_order':m,'tolerance':str(eps),'M_sufficient_for_this_envelope':M,'scope':'raw jet only; no native pivot sign or optimal cutoff'})
result={'status':'PASS','exact_acceleration_checks':accel,'native_cell_checks':cell_checks,
 'native_clock_checks':clock_checks,'max_observed_cell_to_bound_ratio':mp.nstr(max_ratio,18),
 'native_finite_windows':windows,'native_accelerated_windows':accelerated,'signed_critical_controls':controls,'raw_bound_cost':costs,
 'native_pivot_sign_proved':False,'infinite_accelerated_remainder_bound_proved':False}
r=Path(__file__).resolve().parent/'evidence'
r.mkdir(exist_ok=True)
(r/'experiment.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
