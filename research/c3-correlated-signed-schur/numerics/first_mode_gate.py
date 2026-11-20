#!/usr/bin/env python3
"""Gate do modo constante: Cauchy no H deslocado PosDef antigo."""
import json,sys
from pathlib import Path
from mpmath import mp
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
mp.dps=380
path=Path('/home/thlinux/momentos/native-jet-vm-20260930/native_jet_exploration/moments512.json')
h=[mp.mpf(x[:900]) for x in json.load(open(path))['moments'][:85]]
rho=mp.mpf('0.0050052441235941160786')
out=[]
for s in (0,1):
 g=[h[s+j]/(h[s]*rho**j) for j in range(84-s)]
 for n in range(1,41):
  A=mp.matrix([[g[i+j] for j in range(n)] for i in range(n)])
  b=mp.matrix([g[i+n] for i in range(n)])
  v=[-x for x in mp.lu_solve(A,b)]+[mp.mpf(1)]
  p=g[2*n]-(b.T*mp.lu_solve(A,b))[0]
  B=sum(v[i]*v[j]*g[i+j+1] for i in range(n+1) for j in range(n+1))
  r=[(i-n)*v[i] for i in range(n)]
  R=sum(r[i]*r[j]*g[i+j+1] for i in range(n) for j in range(n))
  u0=sum(r[i]*g[i+1] for i in range(n))
  l0=u0*u0/g[1]
  alpha=(2*n+s+1)*(4*n+2*s+3);beta=16*n+8*s+6
  cost=alpha*abs(B)+beta*abs(v[n-1]*p)
  gap=g[2*n+1]-g[2*n]**2/g[2*n-1]
  cost_floor=alpha*abs(B-gap)+beta*abs(v[n-1]*p)
  # projection onto {1,x} in the weighted shifted inner product:
  u1=sum(r[i]*g[i+2] for i in range(n))
  if n>=2:
   M=mp.matrix([[g[1],g[2]],[g[2],g[3]]])
   uu=mp.matrix([u0,u1])
   l2=(uu.T*mp.lu_solve(M,uu))[0]
  else:l2=l0
  row={"s":s,"n":n,
    "first_mode_fraction":mp.nstr(l0/R,20),
    "first_two_fraction":mp.nstr(l2/R,20),
    "first_mode_cost_ratio":mp.nstr(cost/(4*l0),18) if l0 else None,
    "first_two_cost_ratio":mp.nstr(cost/(4*l2),18) if l2 else None,
    "first_mode_floor_cost_ratio":mp.nstr(cost_floor/(4*l0),18) if l0 else None,
    "u0":mp.nstr(u0,24), "l0":mp.nstr(l0,24),
    "full_R":mp.nstr(R,24)}
  out.append(row)
 for z in out:
  if z["s"]==s and z["n"] in [1,2,3,4,5,8,20,40]:print(z,flush=True)
 print('SECTOR',s,'FIRST_MODE gate fail',[z["n"] for z in out if z["s"]==s and (z["first_mode_cost_ratio"] is None or mp.mpf(z["first_mode_cost_ratio"])>=1)],flush=True)
 print('SECTOR',s,'FIRST_TWO gate fail',[z["n"] for z in out if z["s"]==s and (z["first_two_cost_ratio"] is None or mp.mpf(z["first_two_cost_ratio"])>=1)],flush=True)
 print('SECTOR',s,'FIRST_MODE floor gate fail',[z["n"] for z in out if z["s"]==s and (z["first_mode_floor_cost_ratio"] is None or mp.mpf(z["first_mode_floor_cost_ratio"])>=1)],flush=True)
Path(__file__).resolve().parent.parent / "evidence" / "first_mode_gate.json".write_text(json.dumps(out,indent=2)+'\n')
