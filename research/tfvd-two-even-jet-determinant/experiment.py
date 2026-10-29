#!/usr/bin/env python3
"""Small C3 source experiment and exact Fraction checks. No moment inputs.
All floating evaluations, including interval-center comparisons, are diagnostics.
"""
from pathlib import Path
from fractions import Fraction as Q
import ast,hashlib,json,mpmath as mp
mp.mp.dps=70
root=Path(__file__).resolve().parent
producer=root.parent/'tfvd-critical-two-port-ledger/experiment.py'
ns={'mp':mp};tree=ast.parse(producer.read_text())
needed={'cells','head_TL','power_tail','c3_tail'}
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in needed],type_ignores=[]),str(producer),'exec'),ns)
def multiplier(z):
 s=mp.mpf('.5')+mp.j*z
 return s*(s-1)/2*mp.power(mp.pi,-s/2)*mp.gamma(s/2)/(1-mp.power(3,1-s))
A=mp.taylor(multiplier,0,6)
def prefix_jets(M):
 tau=[mp.mpc(0) for r in range(7)]
 for logn,w in ns['cells'](M):
  for r in range(7):tau[r]+=w*mp.exp(-logn/2)*(-mp.j*logn)**r/mp.factorial(r)
 # cells already contains the original unit seed exactly once.
 return [sum(A[j]*tau[r-j] for j in range(r+1)) for r in range(7)]
def even(v):return [v[j] for j in (0,2,4,6)]
def polar(a,b,c,d):return a[0]*b[1]*c[1]*d[2]+3*a[0]*b[0]*c[1]*d[3]-4*a[0]*b[0]*c[2]*d[2]
def quartic(v):return polar(v,v,v,v)
def add(a,b):return [x+y for x,y in zip(a,b)]
def sub(a,b):return [x-y for x,y in zip(a,b)]
def flux(a,e):
 b=add(a,e)
 return polar(e,b,b,b)+polar(a,e,b,b)+polar(a,a,e,b)+polar(a,a,a,e)
fmt=lambda z:mp.nstr(z,40)
reference=[Q(497120778188314,10**15),Q(-11485972157573,10**15),Q(123452018070,10**15),Q(-832355481,10**15)]
assert quartic(reference)>Q(1,10**10)
assert quartic(reference)-32*Q(1,10**12)>Q(1,2*10**10)
runs=[]
for J in (64,128):
 cc=ns['cells'](J)
 def full(z):
  s=mp.mpf('.5')+mp.j*z
  return multiplier(z)*(ns['head_TL'](s,cc)[0]+ns['c3_tail'](s,J))
 f=mp.taylor(full,0,6);v=even(f);rows=[]
 for M in (0,1,2,4,8,16,32,64,128):
  hv=prefix_jets(M);h=even(hv);t=sub(v,h)
  err=quartic(v)-quartic(h)-flux(h,t)
  assert abs(err)<mp.mpf('1e-60')
  increment=quartic(h)-quartic(even(prefix_jets(M-1))) if M else 0
  rows.append({'M':M,'head_quartic':fmt(quartic(h)),
   'last_cell_increment':fmt(increment),'joint_tail_contribution':fmt(flux(h,t)),
   'head_first_odd_jet':fmt(hv[1]),'full_minus_head_plus_tail_error':fmt(abs(err))})
 # Full recombination, no artificial projection of any odd coefficient to zero.
 errors=[abs(vj-mp.mpf(r.numerator)/r.denominator) for vj,r in zip(v,reference)]
 assert max(errors)<mp.mpf('1e-12')
 assert abs(quartic(v).imag)<mp.mpf('1e-60')
 runs.append({'prefix_J':J,'full_even_jets':[fmt(z) for z in v],
   'full_odd_jets':[fmt(f[r]) for r in (1,3,5)],'quartic_full':fmt(quartic(v)),
   'normalized_determinant_diagnostic':fmt(quartic(v)/v[0]**4),
   'max_observed_error_to_rational_centers':fmt(max(errors)),'cutoffs':rows})
 print('C3 source prefix',J,'PASS finite joint diagnostics',flush=True)
# Independent finite rational test of the ordered four-slot expansion.
for k in range(1,21):
 a=[Q((j+1)*k,100) for j in range(4)]
 e=[Q((-1)**j*(j+k),10000) for j in range(4)]
 assert quartic(add(a,e))-quartic(a)==flux(a,e)
result={'status':'PASS_EXACT_RATIONAL_AND_FLOATING_DIAGNOSTICS',
 'source_boxes_kernel_certified':False,'new_native_sign_proved':False,'all_order_positivity_proved':False,
 'producer_uses_moments_zeta_theta_zeros_or_heights':False,
 'source_evaluator_sha256':hashlib.sha256(producer.read_bytes()).hexdigest(),
 'reference_source':'original C3 value with Xi/chart and Taylor/EM exact-tail approximation',
 'tolerance_is_absolute_in_factorial_normalized_Taylor_jets':'1/1000000000000',
 'reference_rationals':[str(v) for v in reference],
 'exact_reference_quartic':str(quartic(reference)),
 'exact_reference_minus_error':str(quartic(reference)-Q(32,10**12)),
 'runs':runs,'interpretation':'Head increments change sign. No formal native no-go or sign follows from floats.'}
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/experiment.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'quartic_reference':result['exact_reference_quartic'],
 'conditional_tolerance':result['tolerance_is_absolute_in_factorial_normalized_Taylor_jets'],
 'native_quartic_diagnostic':runs[-1]['quartic_full'],
 'source_boxes_kernel_certified':False},indent=2))
