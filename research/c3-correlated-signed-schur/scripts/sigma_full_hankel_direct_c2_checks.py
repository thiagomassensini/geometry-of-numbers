#!/usr/bin/env python3
"""Independent direct displaced C2 head+Hurwitz EXACT tail verification of
the first FULL Hankel negative dimension. Numerical, no interval proof."""
import sys, json
from pathlib import Path
import mpmath as mp
SRC=Path('/home/thlinux/momentos/investigations/c2_sigma_crossing_even_jet_hierarchy_20261105')
sys.path.insert(0,str(SRC))
from c2_window_first_negative import moments
OUTPUT=Path(__file__).with_name('sigma_full_hankel_direct_c2_checks.json')
def ldl(h,s,N):
  A=[[mp.mpf('0') for _ in range(N)] for _ in range(N)]
  D=[]
  for k in range(N):
    p=h[s+2*k]-mp.fsum(A[k][j]**2*D[j] for j in range(k))
    D.append(p)
    if p<=0: return k+1,mp.nstr(p,30)
    A[k][k]=1
    for i in range(k+1,N):
      A[i][k]=(h[s+k+i]-mp.fsum(A[i][j]*A[k][j]*D[j] for j in range(k)))/p
  return None,None
records=[]
for d,N,prec,points in [('0.2',7,165,224),('0.00001',10,235,256)]:
    mp.mp.dps=prec
    h,jumps=moments(d,2*N+1,L=12,points=points,radius='0.25')
    q={'d':d,'Nmax':N,'precision':prec,'points':points,
       'max_log_jump':jumps,
       'results':{str(s):{'first_full_negative_dimension':ldl(h,s,N)[0],
                     'negative_pivot':ldl(h,s,N)[1]} for s in [0,1]}}
    records.append(q)
    print(q,flush=True)
OUTPUT.write_text(json.dumps({'method':'direct ORIGINAL C2 finite bracket head+Hurwitz tail (exact) + camera + Gamma completion; Cauchy Fourier extraction; not interval certified','rows':records},indent=2)+'\n')
print('WROTE',OUTPUT,flush=True)
