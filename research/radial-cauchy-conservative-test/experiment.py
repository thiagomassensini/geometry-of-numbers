#!/usr/bin/env python3
"""Exact radial conservative controls + finite ORIGINAL-source diagnostics.
No zeta, theta table, moments checkpoint, zeros or heights as inputs.
Floating source samples are NOT interval certificates.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=50

def symbol(k,j):return Q(2*j+1-k,2*j+k+3)
def port(k,j):return Q(2*(k+1),2*j+k+3)
for k in (0,1,7,31,127):
 for i in range(5):
  for j in range(5):
   assert Q(k+1,i+j+2)*(1-symbol(k,i)*symbol(k,j))==port(k,i)*port(k,j)
   r=Q(2*j+1,2*j+3);a=Q(k,k+2)
   assert symbol(k,j)==(r-a)/(1-a*r)

def logD(t):
 s=mp.mpf('.5')+1j*t
 u=2**(-s);v=2**(1-s)
 up=-1j*mp.log(2)*u;vp=-1j*mp.log(2)*v
 return 1j/s+1j/(s-1)-1j*mp.log(mp.pi)/2+1j*mp.digamma(s/2)/2-(up/(1+u)-vp/(1-v))
def dressing(t):
 s=mp.mpf('.5')+1j*t
 return mp.mpf('.5')*s*(s-1)*mp.exp(-s*mp.log(mp.pi)/2)*mp.gamma(s/2)/((1+2**(-s))*(1-2**(1-s)))

def material(M):
 coeff={}
 for m in range(M):
  for n,w in ((4*m+3,1),(4*m+4,-2),(4*m+5,1)):
   coeff[n]=coeff.get(n,Q(0))+w
 a=4*M+3
 for n,w in ((a,Q(5,8)),(a+1,Q(-1)),(a+2,Q(3,8))):coeff[n]=coeff.get(n,Q(0))+w
 return [(mp.log(n),mp.mpf(w.numerator)/w.denominator) for n,w in coeff.items()]
def source(t,cells):
 s=mp.mpf('.5')+1j*t
 ss=[mp.mpc(1),mp.mpc(0),mp.mpc(0)]
 for l,w in cells:
  v=w*mp.exp(-s*l)
  ss[0]+=v;ss[1]+=-1j*l*v;ss[2]+=-l*l*v
 d=dressing(t);ld=logD(t)
 return d*ss[0],d*(ss[1]+ld*ss[0]),d*(ss[2]+2*ld*ss[1]+(ld**2+mp.diff(logD,t))*ss[0])
def inner(k,c,d):return (k+1)*sum(mp.conj(a)*b/mp.mpf(i+j+2) for i,a in enumerate(c) for j,b in enumerate(d))
def norm2(k,c):return inner(k,c,c).real

tables=[]
for M in (2048,4096):
 cells=material(M)
 F0,Fp0,Fpp0=source(0,cells)
 h0=(-Fpp0/(2*F0)).real
 rows=[]
 for k in (15,31,63,127,255):
  amps=[];qs=[]
  for j in range(2):
   z=1j*mp.mpf(j+1)/(k+1)
   f,fp,_=source(z,cells)
   ep=-fp+1j*f;en=-fp-1j*f
   amps.append(ep/(mp.sqrt(2)*F0));qs.append(en/ep)
  p=[mp.mpf(symbol(k,j).numerator)/symbol(k,j).denominator for j in range(2)]
  ds=[mp.mpf(port(k,j).numerator)/port(k,j).denominator for j in range(2)]
  for sector,c in [('even',[amps[0],mp.mpc(0)]),('odd',[-amps[0]/(1j/(k+1)),amps[1]/(1j/(k+1))])]:
   cc=[a*b for a,b in zip(c,p)];rr=[a*b for a,b in zip(c,qs)];eta=[a-b for a,b in zip(rr,cc)]
   head=abs(sum(a*b for a,b in zip(c,ds)))**2
   signed=norm2(k,c)-norm2(k,rr)
   error=norm2(k,eta);cross=2*inner(k,cc,eta).real
   assert abs(signed-(head-cross-error))<mp.mpf('1e-35')
   assert abs(norm2(k,c)-norm2(k,cc)-head)<mp.mpf('1e-35')
   rows.append({'k':k,'sector':sector,'native_balance':mp.nstr(signed,20),
    'candidate_port_energy':mp.nstr(head,20),'defect_energy':mp.nstr(error,20),
    'mixed_cross':mp.nstr(cross,20)})
  assert abs((k+1)*(qs[0]-p[0])-4*(h0-1))<mp.mpf('.8')
 tables.append({'finite_cells':M,'h0_from_finite_source_curvature':mp.nstr(h0,25),
  'predicted_even_cross_limit':mp.nstr(2*(1-h0),25),'rows':rows})
 print('finite original-source cells',M,flush=True)
result={'status':'EXACT_CONTROLS_AND_FINITE_DIAGNOSTICS','exact_rank_one_controls':125,
 'source':'original center-leg cells, accelerated boundary, Gamma dressing and native chiral quotient',
 'interval_certificate':False,'all_order_canonical_positivity':False,'tables':tables}
out=Path(__file__).resolve().parent/'evidence';out.mkdir(exist_ok=True)
(out/'experiment.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'exact_controls':125,'last_even':tables[-1]['rows'][-2],
 'last_odd':tables[-1]['rows'][-1]},indent=2))
