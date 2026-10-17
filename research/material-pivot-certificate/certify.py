#!/usr/bin/env python3
"""Rational interval certificate for the unchanged theta source; no cached inputs.

The analytic justification of the quadrature and infinite tails is in REPORT.md.
All enclosure arithmetic uses fractions with outward rounding to 70 decimals.
"""
from fractions import Fraction as F
from math import factorial, comb
import argparse, json, time
from pathlib import Path
S=10**70

def fl(x): return F((x*S).numerator//(x*S).denominator,S)
def ce(x): return -fl(-x)
class I:
 def __init__(self,l,u=None): self.l=fl(F(l)); self.u=ce(F(l) if u is None else F(u)); assert self.l<=self.u
 def __add__(s,o):o=cv(o);return I(s.l+o.l,s.u+o.u)
 __radd__=__add__
 def __neg__(s):return I(-s.u,-s.l)
 def __sub__(s,o):return s+-cv(o)
 def __rsub__(s,o):return cv(o)+-s
 def __mul__(s,o):
  o=cv(o); v=[s.l*o.l,s.l*o.u,s.u*o.l,s.u*o.u];return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(s,o):
  o=cv(o);assert not o.l<=0<=o.u,(float(o.l),float(o.u));return s*I(1/o.u,1/o.l)
 def __rtruediv__(s,o):return cv(o)/s
 def __pow__(s,n):
  assert isinstance(n,int) and n>=0
  if n==0:return I(1)
  if n%2:return I(s.l**n,s.u**n)
  return I(0 if s.l<=0<=s.u else min(s.l**n,s.u**n),max(s.l**n,s.u**n))
 def record(s):return dict(lower=str(s.l),upper=str(s.u),lower_decimal=format(float(s.l),'.16e'),upper_decimal=format(float(s.u),'.16e'),width=format(float(s.u-s.l),'.3e'))
cv=lambda x:x if isinstance(x,I) else I(x)
PI=I(F(314159265358979323846,10**20),F(314159265358979323847,10**20))

def exp_pos(x):
 """x>=0, exp(x/1024) Taylor40 with geometric remainder, then ten squares."""
 assert 0<=x<=1024
 y=I(x/1024);term=I(1);poly=term
 for k in range(1,40):term=term*y/k;poly+=term
 rem=(y**40)*F(41,40*factorial(40))
 r=I(poly.l,poly.u+rem.u)
 for _ in range(10):r=r*r
 return r

def exp(x):
 x=cv(x)
 def val(q):return exp_pos(q) if q>=0 else 1/exp_pos(-q)
 return I(val(x.l).l,val(x.u).u)

def polynomials(n):
 P=[[F(1)]]
 for r in range(n):
  a=P[-1];out=[F(0)]*(len(a)+1)
  for j,v in enumerate(a):out[j]+=(F(1,2)+2*j)*v;out[j+1]-=2*v
  P.append(out)
 return P

def evaluate(p,q):
 r=I(0)
 for a in reversed(p):r=r*q+a
 return r

def quadrature(mode,L,grid,order):
 P=polynomials(order);count=int(L*grid);assert count==L*grid
 A=[I(0) for _ in range(10)];error=[F(0) for _ in range(10)]
 for j in range(count):
  a=F(j,grid);b=F(j+1,grid)
  qa=PI*mode**2*exp(2*a);qb=PI*mode**2*exp(2*b)
  fa=2*exp(a/2)/exp(qa)
  ds=[evaluate(p,qa)*fa for p in P[:-1]]
  C=evaluate([abs(v) for v in P[-1]],I(qb.u)).u*fa.u
  for idx in range(10):
   p=idx*2
   # Integral x^p (x-a)^r, expanded around a with positive coefficients.
   weights=[sum(F(comb(p,k))*a**(p-k)*(b-a)**(k+r+1)/F(k+r+1) for k in range(p+1)) for r in range(order+1)]
   poly=sum((ds[r]*(weights[r]/factorial(r)) for r in range(order)),I(0))
   e=C*weights[order]/factorial(order-1) # Mathlib mean-remainder convention
   A[idx]+=poly+I(-e,e);error[idx]+=e
 # For v>=L, mode(L+v)/mode(L) <= exp(-(2q(L)-1/2)*v).
 # (L+v)^p <= L^p exp((p/L)*v).
 qL=PI*mode**2*exp(2*L);fL=2*exp(L/2)/exp(qL)
 for idx in range(10):
  p=2*idx;decay=2*qL.l-F(1,2)-F(p)/L;assert decay>0
  tail=fL.u*L**p/decay
  A[idx]+=I(0,tail)
 return A,error

def eliminate(A):
 c=[F(1,2)-A[0]/4]+[(-1)**n*(A[n-1]/factorial(2*n-2)-A[n]/(4*factorial(2*n))) for n in range(1,10)]
 h=[]
 for n in range(9):h.append((-(n+1)*c[n+1]-sum((h[k]*c[n-k] for k in range(n)),I(0)))/c[0])
 R=[[h[i+j+2]-h[i+1]*h[j+1]/h[0] for j in range(4)] for i in range(4)]
 Q=I(0);pivots=[]
 for r in range(4):
  pivots.append(R[r][r])
  if r==3:break
  Q+=R[3][r]*R[r][3]/R[r][r]
  R=[[R[i][j]-R[i][r]*R[r][j]/R[r][r] if i>r and j>r else R[i][j] for j in range(4)] for i in range(4)]
 T=h[4]*h[4]/h[0]+Q
 B=-(sum((h[k]*c[8-k] for k in range(8)),I(0))+c[0]*T)/9
 return c,h,pivots,B

def main():
 if not __debug__:raise RuntimeError('Run without -O: certificate preconditions must be checked')
 ap=argparse.ArgumentParser();ap.add_argument('--grid',type=int,default=64);ap.add_argument('--order',type=int,default=16);ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
 start=time.time();A=[I(0) for _ in range(10)];parts=[]
 for mode,L in [(1,F(3,2)),(2,F(1)),(3,F(3,4))]:
  v,e=quadrature(mode,L,args.grid,args.order);A=[x+y for x,y in zip(A,v)]
  parts.append(dict(mode=mode,cutoff=str(L),moments=[x.record() for x in v],quadrature_error=[str(x) for x in e]))
  print('mode',mode,'done',round(time.time()-start,2),flush=True)
 # n>=4: pi>=3; n^2>=16+8(n-4), and exp(2u)>=1+2u.
 # sum_{n>=4} 2 exp(u/2-pi*n^2*exp(2u))
 # <= 2 exp(-48)/(1-exp(-24)) exp(-95u) <= 1e-20 exp(-95u).
 e48=exp(48);e24=exp(24)
 assert (2/e48/(1-1/e24)).u<F(1,10**20)
 for k in range(10):A[k]+=I(0,F(factorial(2*k),10**20*95**(2*k+1)))
 c,h,pivots,B=eliminate(A)
 rec=dict(status='RATIONAL_INTERVAL_SOURCE_CERTIFICATE_ANALYTIC_LINK_NOT_YET_LEAN',grid=args.grid,order=args.order,
  pi=PI.record(),source_moments=[x.record() for x in A],characteristic=[x.record() for x in c],moments=[x.record() for x in h],pivots=[x.record() for x in pivots],ceiling=B.record(),c9_gap=(B-c[9]).record(),theta_gap=((1224*A[8]-A[9])+4*factorial(18)*B).record(),parts=parts,seconds=time.time()-start)
 args.out.write_text(json.dumps(rec,indent=2)+'\n')
 print(json.dumps({k:rec[k] for k in ['pivots','ceiling','c9_gap','theta_gap','seconds']},indent=2),flush=True)
 assert all(x.l>0 for x in pivots)
 assert (B-c[9]).l>0
if __name__=='__main__':main()
