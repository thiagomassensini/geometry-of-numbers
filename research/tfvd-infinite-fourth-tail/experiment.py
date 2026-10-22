#!/usr/bin/env python3
"""Finite native regressions, exact envelopes and costs; no zeros or theta inputs."""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=65

def d2(f,a):return f(a+2)-2*f(a+1)+f(a)
def d4(f,a):return f(a+4)-4*f(a+3)+6*f(a+2)-4*f(a+1)+f(a)
def bnd(f,a):return (3*f(a+2)-8*f(a+1)+5*f(a))/8
def rem(f,a):return mp.mpf(3)/8*d4(f,a)+mp.mpf(1)/2*d4(f,a+1)+mp.mpf(3)/8*d4(f,a+2)

envelope_checks=0
for M in [1,2,4,16,501]:
 for N in [0,1,2,16,128]:
  value=sum((F(1,(4*(k+M)+3)**4) for k in range(N)),F())
  bound=F(1,12*(4*M-1)**3)-F(1,12*(4*(N+M)-1)**3)
  assert value<=bound
  envelope_checks+=1
for m in range(11):
 for M in [1,2,16,64,501]:
  a=4*M-1
  old=F(2**(m+1),4*a)
  new=F(30*2**m,12*a**3)
  oldclock=F((m+1)*2**(m+2),4*a)
  newclock=F((m+1)*30*2**(m+1),12*a**3)
  assert new/old==newclock/oldclock==F(5,a*a)
  envelope_checks+=1

def first_strict_cutoff(coefficient,power,epsilon,denominator_coefficient=1):
 lo,hi=1,1
 def sufficient(M):return F(coefficient,denominator_coefficient*(4*M-1)**power)<epsilon
 while not sufficient(hi):hi*=2
 while lo<hi:
  mid=(lo+hi)//2
  if sufficient(mid):hi=mid
  else:lo=mid+1
 return lo
costs=[]
for eps in [F(1,10**8),F(1,10**25)]:
 for kind,cold,cnew in [('ordinary',16,80),('clock',192,960)]:
  old=first_strict_cutoff(cold,1,eps)
  new=first_strict_cutoff(cnew,3,eps)
  costs.append({'jet_order':5,'channel':kind,'tolerance':str(eps),
    'old_envelope_M':old,'accelerated_envelope_M':new,
    'scope':'one raw jet error; no completed multiplier or critical pivot margin'})
assert costs[0]['accelerated_envelope_M']==501
assert costs[1]['accelerated_envelope_M']==1145

@lru_cache(None)
def sample(m,n):
 return mp.power(n,mp.mpf('-0.5'))*(-1j*mp.log(n))**m/mp.factorial(m)
checks=0
for m in range(9):
 for a in [1,2,3,7,67,259,2003]:
  f=lambda n:sample(m,n)
  assert abs(d4(f,a))<=mp.mpf(24)*2**m/a**4
  assert abs(bnd(f,a))<=mp.mpf(2)**m/a
  assert abs(rem(f,a))<=mp.mpf(30)*2**m/a**4
  clock=lambda n:mp.log(n)*sample(m,n)
  assert abs(bnd(clock,a)-1j*(m+1)*bnd(lambda n:sample(m+1,n),a))<mp.mpf('1e-45')
  checks+=1
# No infinite reference value: compare two finite observations with proven tail budgets.
reference=2048
windows=[]
for m in [0,1,3,5,6]:
 f=lambda n:sample(m,n)
 prefix=[mp.mpc(0)]
 for k in range(reference):prefix.append(prefix[-1]+d2(f,4*k+3))
 ref=prefix[reference]+bnd(f,4*reference+3)
 for M in [4,16,64,256,501]:
  approx=prefix[M]+bnd(f,4*M+3)
  error=mp.mpf(30)*2**m/(12*(4*M-1)**3)
  ref_error=mp.mpf(30)*2**m/(12*(4*reference-1)**3)
  assert abs(approx-ref)<=error+ref_error
  windows.append({'m':m,'M':M,'reference_M':reference,
   'finite_observation_difference':mp.nstr(abs(approx-ref),20),
   'proved_envelope_sum':mp.nstr(error+ref_error,20)})
# Preserve both endpoints in a native finite-window identity.
identities=0
for m in [0,1,5,6]:
 f=lambda n:sample(m,n)
 for M,N in [(1,1),(4,16),(16,128)]:
  a=4*M+3
  lhs=sum((d2(f,a+4*k) for k in range(N)),mp.mpc(0))
  rhs=bnd(f,a)-bnd(f,a+4*N)+sum((rem(f,a+4*k) for k in range(N)),mp.mpc(0))
  assert abs(lhs-rhs)<mp.mpf('1e-45')
  identities+=1
result={'status':'PASS','exact_quartic_envelope_and_gain_checks':envelope_checks,
 'native_fourth_boundary_clock_checks':checks,'native_finite_identity_checks':identities,
 'finite_observation_comparisons':windows,'cutoff_costs':costs,
 'native_pivot_sign_proved':False,'all_order_Hankel_positivity_proved':False,
 'note':'Infinite bounds are proved by Lean; mpmath is a finite regression, not an interval certificate.'}
evidence=Path(__file__).resolve().parent/'evidence'
evidence.mkdir(exist_ok=True)
(evidence/'experiment.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
