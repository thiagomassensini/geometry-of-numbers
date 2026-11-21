#!/usr/bin/env python3
"""Full Hankel LDL probe from original C2 central jets. NUMERICAL, not interval certified."""
from pathlib import Path
import json,math,mpmath as mp
SOURCE=Path('/home/thlinux/momentos/investigations/c2_sigma_crossing_even_jet_hierarchy_20261105/quartic_frontier_native_strip.json')
OUT=Path(__file__).with_name('sigma_full_hankel_ldl_probe.json')
J=json.loads(SOURCE.read_text());mp.mp.dps=180
H=[mp.mpf(z) for z in J['central_moments']]
def jet(n,d,cap):
  jmax=min(len(H)-1-n,cap)
  return mp.fsum((-1)**j*mp.mpf(math.comb(2*n+2*j+1,2*j))*H[n+j]*d**(2*j) for j in range(jmax+1))
def ldl(h,s,N):
  L=[[mp.mpf('0') for _ in range(N)] for _ in range(N)];D=[]
  for k in range(N):
    z=h[s+2*k]-mp.fsum(L[k][j]**2*D[j] for j in range(k))
    D.append(z)
    if z<=0: return k+1,mp.nstr(z,30),''.join('+' if t>0 else '-' for t in D)
    L[k][k]=1
    for i in range(k+1,N):
      z=h[s+k+i]-mp.fsum(L[i][j]*L[k][j]*D[j] for j in range(k))
      L[i][k]=z/D[k]
  return None,None,''.join('+' if t>0 else '-' for t in D)
def probe(d,N,cap):
  h=[jet(n,d,cap) for n in range(2*N)]
  ans={}
  for s in [0,1]:
    n,z,signs=ldl(h,s,N)
    first_window=next((s+i for i in range(2*N-s-2) if h[s+i]*h[s+i+2]-h[s+i+1]**2<0),None)
    ans[str(s)]={'first_full_negative_dimension':n,'negative_pivot':z,'ldl_signs':signs,'first_adjacent_window_negative_shift_in_sample':first_window}
  return ans
rows=[]
for ds in ['0','0.2','0.1','0.05','0.02','0.01','0.001','0.00001','0.0000001','0.000000001','0.00000000001','0.0000000000001','0.000000000000001']:
 d=mp.mpf(ds)
 N=11 if abs(d)>=mp.mpf('0.01') else 17
 caps=[None,12,18]
 caplist=[len(H)-1 if c is None else c for c in caps]
 outputs=[probe(d,N,c) for c in caplist]
 row={'d':ds,'Nmax':N,'first':outputs[0], 'same_with_12_terms':outputs[0]==outputs[1], 'same_with_18_terms':outputs[0]==outputs[2]}
 rows.append(row)
 print(ds,row,flush=True)
OUT.write_text(json.dumps({'method':'C2 central moments from exact head+tail plus local transverse Taylor; no zeros input; 180 dps not interval certified','source':str(SOURCE),'rows':rows},indent=2)+'\n')
print('WROTE',OUT,flush=True)
