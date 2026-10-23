#!/usr/bin/env python3
"""Original C3 TFVD heads and completed response; no zeta/theta/zeros input.
The infinite tail is numerically approximated by a Taylor/EM expansion.
All floating results are diagnostics, not interval or Lean sign certificates.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,math
import mpmath as mp
mp.mp.dps=70
root=Path(__file__).resolve().parent
reference=json.loads((root/'reference-moments.json').read_text())
h0,h1,h2=[mp.mpf(t) for t in reference['moments'][:3]]
a=-h1/h0

def cells(M):
 d={1:1}
 for m in range(1,M+1):
  for n,w in ((3*m-1,1),(3*m,-2),(3*m+1,1)):
   d[n]=d.get(n,0)+w
 return [(mp.log(n),w) for n,w in d.items() if w]

head_cells={M:cells(M) for M in (0,1,2,4,16,64)}
def head_TL(s,cc):
 T=mp.mpc(0);L=mp.mpc(0)
 for logn,w in cc:
  z=w*mp.exp(-s*logn);T+=z;L+=logn*z
 return T,L

def base(s):
 Qc=1-mp.power(3,1-s)
 Qp=mp.log(3)*mp.power(3,1-s)
 return -1/s-1/(s-1)+mp.log(mp.pi)/2-mp.digamma(s/2)/2+Qp/Qc

def power_tail(p,A,em=8):
 out=mp.power(A,1-p)/(p-1)+mp.power(A,-p)/2
 for j in range(1,em+1):
  out+=mp.bernoulli(2*j)/mp.factorial(2*j)*mp.rf(p,2*j-1)*mp.power(A,-p-2*j+1)
 return out

def c3_tail(s,J,terms=10,em=8):
 return sum(2*mp.rf(s,2*l)/mp.factorial(2*l)*mp.power(3,-s-2*l)*
   power_tail(s+2*l,mp.mpf(J+1),em) for l in range(1,terms+1))

def full_TL(s,J,cc):
 T,L=head_TL(s,cc)
 tail=c3_tail(s,J)
 logtail=-mp.diff(lambda ss:c3_tail(ss,J),s)
 return T+tail,L+logtail

def pairing(K,v,w):
 return K*sum(mp.conj(v[i])*w[j]/(i+j+2) for i in range(len(v)) for j in range(len(w)))
def flux(K,v,theta):
 return pairing(K,v,[b*c for b,c in zip(theta,v)]).imag

def direct_form(K,v,theta):
 inc=[c*(b+1j)/mp.sqrt(2) for b,c in zip(theta,v)]
 ret=[c*(b-1j)/mp.sqrt(2) for b,c in zip(theta,v)]
 return (pairing(K,inc,inc)-pairing(K,ret,ret)).real/2

def fmt(x):return mp.nstr(x,25)

# Independent rational control for the exact Gram norm of the highest jet profile.
for m in range(9):
 v=[Q((-1)**(m-j)*math.comb(m,j),math.factorial(m)) for j in range(m+1)]
 gram=sum(v[i]*v[j]/Q(i+j+2) for i in range(m+1) for j in range(m+1))
 assert gram==Q(1,math.factorial(m)**2*(2*m+1)*(2*m+2))

center_heads=[]
for M,cc in head_cells.items():
 T,L=head_TL(mp.mpf('.5'),cc)
 center_heads.append({'M':M,'head_response_imaginary_at_center':fmt((base(mp.mpf('.5'))+L/T).real),
  'formal_sign_certificate':False})

runs=[]
for J in (128,256):
 cc=cells(J)
 T0,L0=full_TL(mp.mpf('.5'),J,cc)
 center=base(mp.mpf('.5'))+L0/T0
 rows=[]
 for K in (32,128,512,2048):
  full=[];heads={M:[] for M in head_cells}
  for j in range(4):
   ss=mp.mpf('.5')-mp.mpf(j+1)/K
   T,L=full_TL(ss,J,cc)
   full.append(1j*(base(ss)+L/T))
   for M,hh in head_cells.items():
    TH,LH=head_TL(ss,hh)
    heads[M].append(1j*(base(ss)+LH/TH))
    # Both tails, not just the log tail, enter the exact crossed determinant.
    err=1j*(TH*(L-LH)-LH*(T-TH))/(TH*T)
    assert abs((full[-1]-heads[M][-1])-err)<mp.mpf('1e-55')
  profiles=[('first_even',0,[mp.mpf(1),mp.mpf(0)],h0),
            ('first_odd',1,[1j*K,-1j*K],h1),
            ('second_even',2,[a-mp.mpf(K)**2/2,mp.mpf(K)**2,-mp.mpf(K)**2/2,0],h2-h1*h1/h0)]
  for name,m,v,target in profiles:
   theta=full[:len(v)];ff=flux(K,v,theta)
   assert abs(ff-direct_form(K,v,theta))<mp.mpf('1e-42')
   for M,hh in heads.items():
    ht=hh[:len(v)];hf=flux(K,v,ht);ef=flux(K,v,[u-w for u,w in zip(theta,ht)])
    assert abs(ff-hf-ef)<mp.mpf('1e-42')
    rows.append({'K':K,'M':M,'sector':name,'native_full_flux':fmt(ff),'head_flux':fmt(hf),
      'correction_flux':fmt(ef),'head_over_radial_growth':fmt(hf/mp.mpf(K)**(2*m+1)),
      'expected_head_scaled_coefficient':fmt((base(mp.mpf('.5'))+head_TL(mp.mpf('.5'),head_cells[M])[1]/head_TL(mp.mpf('.5'),head_cells[M])[0]).real/
          (mp.factorial(m)**2*(2*m+1)*(2*m+2))),
      'moment_reference_limit':fmt(target)})
  print('tail prefix',J,'radial K',K,flush=True)
 runs.append({'tail_prefix_J':J,'taylor_terms':10,'euler_maclaurin_terms':8,
  'unforced_full_response_at_center':fmt(center),'rows':rows})

# Compare the two independently truncated approximations of the SAME complete source.
max_gap=max(abs(mp.mpf(x['native_full_flux'])-mp.mpf(y['native_full_flux']))
 for x,y in zip(runs[0]['rows'],runs[1]['rows']))
result={'scope':'Native C3 finite heads + numerical Taylor/EM tail + original Xi/chart completion',
 'status':'PASS_ALGEBRA_AND_FINITE_DIAGNOSTICS','source_sign_certificate':False,
 'source_evaluator_uses_zeta_theta_zeros_or_heights':False,
 'stored_moments_used_only_for_direction_and_comparison':True,
 'reference_decimals_scope':reference['scope'],'center_heads':center_heads,'runs':runs,
 'max_complete_flux_difference_two_tail_prefixes':fmt(max_gap),
 'all_order_positivity_proved':False,'numeric_digits_are_not_certified':True}
(root/'evidence/experiment.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'center_heads':center_heads,'max_complete_flux_gap':fmt(max_gap),
 'K2048_M2':[r for r in runs[-1]['rows'] if r['K']==2048 and r['M']==2]},indent=2))
