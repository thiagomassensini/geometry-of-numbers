#!/usr/bin/env python3
"""Exact rational reproduction of the attached Schur test and logical controls.
Reference decimals are data, not an original-source integral certificate.
"""
from pathlib import Path
from fractions import Fraction as Q
from decimal import Decimal,localcontext
import json
root=Path(__file__).resolve().parent
ref=json.loads((root/'reference-moments.json').read_text())
h=[Q(x) for x in ref['moments']]
a,b,d=h[:3];b0,b1=h[2:4]
det=a*d-b*b
assert a>0 and det>0
x0=(d*b0-b*b1)/det;x1=(a*b1-b*b0)/det
v=[-x0,-x1,Q(1)]
threshold=b0*x0+b1*x1;p=h[4]-threshold
energy=sum(v[i]*h[i+j]*v[j] for i in range(3) for j in range(3))
assert energy==p and p>0
# Reuse the PR41 null/future-crossing control: this is NOT the canonical source.
control=[Q(1),Q(0),Q(0),Q(1),Q(0)];z=[Q(0),Q(1)]
beta=sum(control[i+2]*z[i] for i in range(2));c=control[4]
w=[-Q(c*c+1,2*beta)*q for q in z]+[Q(1)]
q=lambda m,y:sum(y[i]*m[i+j]*y[j] for i in range(len(y)) for j in range(len(y)))
assert q(control,z)==0 and beta==1 and q(control,w)==-1
# Check the constructive singular witness for several arbitrary last diagonals.
for c in [Q(-9),Q(-1),Q(0),Q(1),Q(7,3)]:
 for beta in [Q(-3),Q(1,2),Q(4)]:
  old=[Q(1),Q(0),Q(0),beta,c]
  ww=[Q(0),-Q(c*c+1)/(2*beta),Q(1)]
  assert q(old,ww)==c-c*c-1<0
# Quantifier control: strict finite amplification need not survive at a FIXED direction.
# D_k(x)=-x^2/(k+1) -> 0 for each fixed x, yet D_k(sqrt(k+1))=-1.
quantifier=[{'k':k,'fixed_excess':str(Q(1,k+1)),'moving_squared_input_norm':k+1,
             'moving_excess':'1'} for k in (1,15,255)]
with localcontext() as ctx:
 ctx.prec=45
 f=lambda x:str(Decimal(x.numerator)/Decimal(x.denominator))
 result={'status':'PASS_EXACT_STORED_DECIMALS_AND_LOGICAL_CONTROLS',
  'reference_source_sha256':ref['sha256'],'scope':ref['scope'],
  'threshold':f(threshold),'h4':f(h[4]),'pivot':f(p),'critical_vector':[f(x) for x in v],
  'exact_witness_energy_equals_pivot':True,
  'pr41_control':{'old_null_energy':'0','new_coupling':'1','explicit_witness':[str(x) for x in w],
   'new_energy':'-1','canonical_source':False},
  'moving_input_control':quantifier,'canonical_negative_direction_found':False}
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/experiment.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
