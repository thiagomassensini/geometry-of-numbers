#!/usr/bin/env python3
"""Run after C3 original diagnostics, reusing exact same source jets.
Joint source-linearized tail budget for S=alpha*B-beta*a*p.
Numerical diagnostic only: |tail_j| are numerically computed, not Lean intervals.
"""
from mpmath import mp
from pathlib import Path
import json
def source_coords(s,n,v):
  zB=source_lift(v if s==0 else [mp.mpf(0)]+list(v))
  zP=source_lift(v)
  return zB,zP,(s==0),(s==1)

def joint_probe(s,n):
  A=mp.matrix([[h[s+i+j] for j in range(n)] for i in range(n)])
  q=mp.matrix([h[s+i+n] for i in range(n)])
  sol=mp.lu_solve(A,q)
  v=[-sol[i] for i in range(n)]+[mp.mpf(1)]
  r=[(i-n)*v[i] for i in range(n)]
  u=mp.fsum(r[i]*h[s+1+i] for i in range(n))
  a=v[n-1]
  alpha=(2*n+s+1)*(4*n+2*s+3)
  beta=16*n+8*s+6
  zB,zP,bB,bP=source_coords(s,n,v)
  B=mp.fsum(v[i]*v[j]*h[s+1+i+j] for i in range(n+1) for j in range(n+1))
  p=mp.fsum(v[i]*v[j]*h[s+i+j] for i in range(n+1) for j in range(n+1))
  S=alpha*B-beta*a*p
  Bhead=term(adj,adj,bB,zB,zB)
  phead=term(adj,adj,bP,zP,zP)
  Shead=alpha*Bhead-beta*a*phead
  EB=budget(adj,tail,bB,zB,zB)+budget(tail,adj,bB,zB,zB)+budget(tail,tail,bB,zB,zB)
  Ep=budget(adj,tail,bP,zP,zP)+budget(tail,adj,bP,zP,zP)+budget(tail,tail,bP,zP,zP)
  Esep=alpha*EB+beta*abs(a)*Ep
  # Group every occurrence of the SAME source tail coefficient
  # before applying its absolute value. Bilinear HT+TH is linear in T.
  L=[]
  for k in range(len(tail)):
    e=[mp.mpc(0)]*len(tail)
    e[k]=mp.mpc(1)
    val=alpha*(term(adj,e,bB,zB,zB)+term(e,adj,bB,zB,zB))
    val-=beta*a*(term(adj,e,bP,zP,zP)+term(e,adj,bP,zP,zP))
    L.append(val)
  linearactual=alpha*(term(adj,tail,bB,zB,zB)+term(tail,adj,bB,zB,zB))-beta*a*(
    term(adj,tail,bP,zP,zP)+term(tail,adj,bP,zP,zP))
  fromcoeff=mp.fsum(L[k]*tail[k] for k in range(len(tail)))
  EgroupLin=mp.fsum(abs(L[k])*abs(tail[k]) for k in range(len(tail)))
  ETT=alpha*budget(tail,tail,bB,zB,zB)+beta*abs(a)*budget(tail,tail,bP,zP,zP)
  Ejoint=EgroupLin+ETT
  # signed gate: W = 4R + S, so estimate S from BELOW.
  # the first-mode lower u from the existing u witness.
  zU=source_lift(r if s==0 else [mp.mpf(0)]+r)
  z0=source_lift([mp.mpf(1)]+[mp.mpf(0)]*(n-1) if s==0 else
    [mp.mpf(0),mp.mpf(1)]+[mp.mpf(0)]*(n-1))
  uHead=term(adj,adj,bB,zU,z0)
  Eu=budget(adj,tail,bB,zU,z0)+budget(tail,adj,bB,zU,z0)+budget(tail,tail,bB,zU,z0)
  Lu=max(mp.mpf(0),abs(uHead.real)-Eu)
  signedGate=(h[s+1]*(Ejoint-Shead.real))/(4*Lu**2) if Lu>0 else mp.inf
  absGate=(h[s+1]*(abs(Shead.real)+Ejoint))/(4*Lu**2) if Lu>0 else mp.inf
  oldGate=(h[s+1]*(alpha*(abs(Bhead.real)+EB)+beta*abs(a)*(abs(phead.real)+Ep)))/(4*Lu**2) if Lu>0 else mp.inf
  return dict(s=s,n=n,S=mp.nstr(S,24),S_head=mp.nstr(Shead.real,24),
    S_head_sign=int(mp.sign(Shead.real)),
    S_actual_abs_error=mp.nstr(abs(S-Shead),12),
    Esep=mp.nstr(Esep,16),EgroupLin=mp.nstr(EgroupLin,16),
    ETT=mp.nstr(ETT,16),Ejoint=mp.nstr(Ejoint,16),
    E_joint_to_sep=mp.nstr(Ejoint/Esep,14),
    lin_reconstruction_error=mp.nstr(abs(fromcoeff-linearactual),12),
    signedGate=mp.nstr(signedGate,16),
    absGate=mp.nstr(absGate,16),
    oldGate=mp.nstr(oldGate,16),
    signedPass=bool(signedGate<1),absPass=bool(absGate<1),
    oldPass=bool(oldGate<1),
    tail_interval_note="Uses computed |tail_j|, not certified intervals")

jointRows=[]
for ss in (0,1):
  for nn in range(1,nmax+1):
    t=joint_probe(ss,nn)
    jointRows.append(t)
    print("JOINT S",ss,nn,"headS",t["S_head_sign"],
          "Ejoint/Esep",t["E_joint_to_sep"],
          "old",t["oldGate"],"abs",t["absGate"],
          "signed",t["signedGate"],"PASS",t["signedPass"],flush=True)
dest=HOME/f"joint_S_M{M}_n{nmax}_numeric.json"
dest.write_text(json.dumps(dict(source_M=M,max_n=nmax,
  status="NUMERICAL_SOURCE_COEFFICIENT_BOUNDS_NOT_CERTIFIED",
  rows=jointRows),indent=2)+"\n")
print("JOINT_FILE",dest,flush=True)
