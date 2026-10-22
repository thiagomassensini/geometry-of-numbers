#!/usr/bin/env python3
"""Exact budgets and finite original-source regressions. No sign certificate.
Gamma arithmetic uses mpmath, not certified rational intervals. No zeta,
zeros, heights, theta data, moment checkpoint or matrix factor is an input.
"""
from fractions import Fraction as F
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=45
orders=6
Ms=[512,4096,100000,101000]
ref=Ms[-1]

def C(r):
 return sum(8192*8**j*2**(r-j+1)+4**j*(r-j+1)*2**(r-j+2) for j in range(r+1))
cs=[C(r) for r in range(6)]
assert cs==[16388,163872,1376432,11141952,89394752,715668480]
budget=F(5)*(C(5)+F(1,50)*C(3)+F(1,10000)*C(1))/F(4*(4*100000-1)**3)
assert budget<F(1,50000000)

def sample(n):
 v=1/mp.sqrt(n);l=mp.log(n)
 out=[v]
 for m in range(1,orders+1):out.append(out[-1]*l/m)
 return out

def boundary(M):
 a=4*M+3
 x,y,z=sample(a),sample(a+1),sample(a+2)
 return [(5*x[m]-8*y[m]+3*z[m])/8 for m in range(orders+1)]

prefix=[mp.mpf(0)]*(orders+1)
signals={}
for k in range(ref):
 x,y,z=sample(4*k+3),sample(4*k+4),sample(4*k+5)
 for m in range(orders+1):prefix[m]+=x[m]-2*y[m]+z[m]
 M=k+1
 if M in Ms:
  bd=boundary(M)
  vals=[(-1j)**m*(prefix[m]+bd[m]) for m in range(orders+1)]
  vals[0]+=1
  signals[M]=vals
  print('finite native jet prefix',M,flush=True)

def conv(x,y,n=5):return [sum(x[j]*y[m-j] for j in range(m+1)) for m in range(n+1)]
def invseries(x):
 y=[1/x[0]]
 for m in range(1,len(x)):y.append(-sum(x[j]*y[m-j] for j in range(1,m+1))/x[0])
 return y

def logD(t):
 s=mp.mpf('.5')+1j*t
 u=mp.power(2,-s);v=mp.power(2,1-s)
 up=-1j*mp.log(2)*u;vp=-1j*mp.log(2)*v
 return 1j/s+1j/(s-1)-1j*mp.log(mp.pi)/2+1j*mp.digamma(s/2)/2-(up/(1+u)-vp/(1-v))

d=mp.taylor(logD,0,5)
Sref=signals[ref]
iS=invseries(Sref)
A=[-v/2 for v in conv(d,iS)]
B=[1j*v/2 for v in iS[:6]]
Q=[-d[m]/2-v/2 for m,v in enumerate(conv([(m+1)*Sref[m+1] for m in range(6)],iS))]
h=[Q[2*n+1].real for n in range(3)]
a=h[1]/h[0]
p=h[2]-h[1]**2/h[0]
assert abs(a)<mp.mpf('0.01')
assert all(abs(A[j])<=8192*8**j and abs(B[j])<=4**j for j in range(6))
windows=[]
for M in Ms[:-1]:
 S=signals[M];K=[1j*(m+1)*S[m+1] for m in range(6)]
 aa,bb=conv(A,S),conv(B,K)
 q=[(aa[m]+bb[m]).real for m in [1,3,5]]
 obs=q[2]-2*a*q[1]+a*a*q[0]
 e=mp.mpf(5)*(C(5)+2*abs(a)*C(3)+a*a*C(1))/(4*(4*M-1)**3)
 assert abs(p-obs)<e
 windows.append({'M':M,'observation_numerical':mp.nstr(obs,25),
  'reference_minus_observation':mp.nstr(p-obs,15),'proved_envelope_evaluated_numerically':mp.nstr(e,15)})
# Verify the original D formula against the factored logarithmic derivative.
def D(t):
 s=mp.mpf('.5')+1j*t
 return mp.mpf('.5')*s*(s-1)*mp.exp(-s*mp.log(mp.pi)/2)*mp.gamma(s/2)/((1+2**(-s))*(1-2**(1-s)))
for t in [mp.mpf('0'),mp.mpf('.01'),mp.mpf('-.03')]:
 assert abs(mp.diff(D,t)/D(t)-logD(t))<mp.mpf('1e-35')
result={'status':'PASS_FINITE_REGRESSION_ONLY','source':'original center-leg cells with the derived accelerated boundary',
 'response_constants':cs,'second_direction_envelope_rational':str(budget),
 'second_direction_envelope_decimal':float(budget),
 'source_cutoffs':Ms,'reference_note':'Finite 101000 reference estimates original multipliers. It is not the complete denominator or a Gamma interval certificate.',
 'canonical_h_numerical_estimates':[mp.nstr(v,30) for v in h],
 'critical_coefficient_numerical':mp.nstr(a,25),'pivot_numerical_estimate':mp.nstr(p,25),
 'multiplier_jet_numerical_estimates':{'A':[mp.nstr(v,18) for v in A],'B':[mp.nstr(v,18) for v in B]},
 'observations':windows,
 'kernel_proves_multiplier_upper_bounds':True,
 'kernel_proves_new_pivot_sign':False,'all_order_positivity_proved':False,
 'remaining_gate':'Enclose the same finite readout values by rational intervals, including Gamma derivatives and the complete reciprocal signal. Norm upper bounds do not certify these centers.'}
evidence=Path(__file__).resolve().parent/'evidence';evidence.mkdir(exist_ok=True)
(evidence/'experiment.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
