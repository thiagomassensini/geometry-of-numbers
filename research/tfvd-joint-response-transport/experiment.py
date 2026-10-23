#!/usr/bin/env python3
"""Small regressions of the recombined C3 producer; no new moment campaign.
The evaluator is reused from PR65 without running its top-level experiments.
Floating values are NOT intervals; exact control values use Fraction.
"""
from pathlib import Path
from fractions import Fraction as Q
import ast
import hashlib
import json
import mpmath as mp
mp.mp.dps=70
root=Path(__file__).resolve().parent
original=root.parent/'tfvd-critical-two-port-ledger'/'experiment.py'
# Reuse only source-evaluator definitions. No old top-level writes or moment read occurs.
names={'cells','head_TL','base','power_tail','c3_tail','full_TL'}
module=ast.parse(original.read_text())
selected=ast.Module(body=[n for n in module.body if isinstance(n,ast.FunctionDef) and n.name in names],type_ignores=[])
ns={'mp':mp}
exec(compile(selected,str(original),'exec'),ns)
cells,head_TL,base,full_TL=[ns[n] for n in ('cells','head_TL','base','full_TL')]
fmt=lambda x:mp.nstr(x,35)

def joint(x,y):
 T,L,B=x;U,V,C=y
 return T*U*(C-B)+1j*(T*V-L*U)

def polarized(x,y):
 T,L,B=x;U,V,C=y
 return mp.conj(T)*U*(C-mp.conj(B))+1j*(mp.conj(T)*V+mp.conj(L)*U)

def theta(x):
 T,L,B=x
 return B+1j*L/T

def build(z,J,cc):
 s=mp.mpf('.5')+1j*z
 T,L=full_TL(s,J,cc)
 return T,L,1j*base(s)

runs=[]
for J in (64,128):
 cc=cells(J)
 points=[mp.mpc('.03','.02'),mp.mpc('-.02','.04'),mp.mpc('.01','.07')]
 states=[build(z,J,cc) for z in points]
 a,b,c=states
 cocycle=b[0]*joint(a,c)-c[0]*joint(a,b)-a[0]*joint(b,c)
 quotient_error=joint(a,c)-a[0]*c[0]*(theta(c)-theta(a))
 polarized_error=polarized(a,c)-mp.conj(a[0])*c[0]*(theta(c)-mp.conj(theta(a)))
 assert max(abs(cocycle),abs(quotient_error),abs(polarized_error))<mp.mpf('1e-60')
 samples=[]
 center=build(0,J,cc)
 for K in (32,128,512):
  z=1j/mp.mpf(K)
  v=build(z,J,cc)
  norm_joint=joint(center,v)/(center[0]*v[0])
  samples.append({'K':K,'joint_normalized_over_2z':fmt(norm_joint/(2*z))})
 # Independent radial endpoints and their original physical Cauchy entry.
 K=32;i=0;j=2
 zi=1j*mp.mpf(i+1)/K;zj=1j*mp.mpf(j+1)/K
 si,sj=build(zi,J,cc),build(zj,J,cc)
 omega=1j*K/(2*(i+j+2))*(mp.conj(theta(si))-theta(sj))
 multiplied=2*(zj-mp.conj(zi))*mp.conj(si[0])*sj[0]*omega
 assert abs(multiplied-polarized(si,sj))<mp.mpf('1e-60')
 runs.append({'tail_prefix_J':J,'composition_error':fmt(abs(cocycle)),
  'quotient_error':fmt(abs(quotient_error)),'polarized_error':fmt(abs(polarized_error)),
  'physical_pairing_error':fmt(abs(multiplied-polarized(si,sj))),'central_samples':samples})
 print('native joint producer: prefix',J,'PASS',flush=True)

K=10
material=[Q(-51),Q(100),Q(-50),Q(0)]
f=lambda y:2*y-2*y**3+y**5
flux=K*sum(material[i]*material[j]*f(Q(j+1,K))/Q(i+j+2)
 for i in range(4) for j in range(4))
assert flux==Q(-6199,20000)
result={'status':'PASS_FINITE_REGRESSIONS','formal_sign_certificate':False,
 'all_order_positivity_proved':False,'source_evaluator_sha256':hashlib.sha256(original.read_bytes()).hexdigest(),
 'uses_zeta_theta_zeros_heights_or_moments_as_producer_input':False,
 'tail_scope':'Taylor/EM diagnostic, not certified interval','native_runs':runs,
 'auxiliary_control':{'is_native_Carry_source':False,'exact_negative_flux':str(flux),
  'response':'2*z+2*z^3+z^5','characteristic':'exp(-z^2-z^4/2-z^6/6)'}}
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence'/'experiment.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
