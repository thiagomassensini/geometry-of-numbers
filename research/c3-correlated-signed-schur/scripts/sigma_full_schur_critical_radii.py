#!/usr/bin/env python3
"""Numerical Schur critical-radius diagnostic from original C2 central moments.
No zeros, no RH, no adapted Gram. Root localization is NOT interval certified.
"""
import mpmath as mp, math, json
from pathlib import Path
P=Path('/home/thlinux/momentos/investigations/c2_sigma_crossing_even_jet_hierarchy_20261105/quartic_frontier_native_strip.json')
Q=Path(__file__).with_name('sigma_full_schur_critical_radii.json')
mp.mp.dps=145
H=[mp.mpf(y) for y in json.loads(P.read_text())['central_moments']]
def moment(k,d):
    z=d*d
    return mp.fsum([H[k+j]*(-z)**j*math.comb(2*k+2*j+1,2*j) for j in range(len(H)-k)])
def pivot(s,n,d):
    # augmented n+1 section, leading n old coefficients
    q=[moment(s+i,d) for i in range(2*n+1)]
    if n==0:return q[0]
    A=mp.matrix([[q[i+j] for j in range(n)] for i in range(n)])
    b=mp.matrix([q[n+i] for i in range(n)])
    return q[2*n]-(b.T*mp.lu_solve(A,b))[0]
def curvature(s,n):
    q=H
    if n==0:v=[mp.mpf('1')]
    else:
      A=mp.matrix([[q[s+i+j] for j in range(n)] for i in range(n)])
      b=mp.matrix([q[s+i+n] for i in range(n)])
      y=mp.lu_solve(A,b)
      v=[-y[i] for i in range(n)]+[mp.mpf('1')]
    p0=pivot(s,n,mp.mpf('0'))
    p2=mp.fsum([-2*v[i]*v[j]*(s+i+j+1)*(2*(s+i+j)+3)*q[s+i+j+1] for i in range(n+1) for j in range(n+1)])
    return p0,p2
def first_root(s,n):
  p0,p2=curvature(s,n)
  assert p0>0
  approx=mp.sqrt(-2*p0/p2) if p2<0 else None
  ds=[mp.mpf('1e-14')*mp.power(10,mp.mpf(k)/8) for k in range(8*14+1)]
  ds=[d for d in ds if 0<d<mp.mpf('0.25')]
  prev=mp.mpf('0')
  for d in ds:
    v=pivot(s,n,d)
    if v<0:
      lo,hi=prev,d
      for _ in range(135):
        mid=(lo+hi)/2
        if pivot(s,n,mid)>0:lo=mid
        else:hi=mid
      r=(lo+hi)/2
      return {'n':n,'dimension':n+1,'root_d':mp.nstr(r,36),
              'p_center':mp.nstr(p0,16),'p_second_deriv':mp.nstr(p2,16),
              'quadratic_root':mp.nstr(approx,36) if approx is not None else None,
              'relative_r2_error':mp.nstr(abs(approx/r-1),12) if approx is not None else None}
    prev=d
  return {'n':n,'dimension':n+1,'root_d':None,'p_center':mp.nstr(p0,16),
          'p_second_deriv':mp.nstr(p2,16),'quadratic_root':mp.nstr(approx,20) if approx is not None else None}
rows={}
for s in [0,1]:
  rows[str(s)]=[]
  for n in range(1,10):
    row=first_root(s,n);rows[str(s)].append(row)
    print('sector',s,'n',n,'root',row['root_d'],'pred',row['quadratic_root'],'rel',row.get('relative_r2_error'),flush=True)
Q.write_text(json.dumps({'source':str(P),'method':'Schur moving pivot from original C2 Taylor moments, exact head and Hurwitz tail at center; 145 dps, roots unverified by intervals','rows':rows},indent=2)+'\n')
print('WROTE',Q)
