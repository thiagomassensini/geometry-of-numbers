#!/usr/bin/env python3
"""Reconstruct finite positive Jacobi spectrum from first 100 canonical moments.

Inputs: moments512.json from native-jet exploration (no zeros supplied).
Interval arithmetic: python-flint Arb tests the 100 decimal-stored moments'
50x50 unshifted and shifted Hankel forms.
Independent mpmath Jacobi spectral decomposition then reconstructs
m_0..m_99 from 50 strictly positive nodes and weights.
IMPORTANT: this is a FINITE statement about the stored decimals, not a
Lean certificate for the exact completed-native infinite moment sequence.
"""
import json, hashlib, sys, time
from pathlib import Path
from flint import arb, ctx
from mpmath import mp

INPUT=Path(sys.argv[1] if len(sys.argv)>1 else
  '/home/thlinux/momentos/native-jet-vm-20260930/native_jet_exploration/moments512.json')
OUTPUT=Path(sys.argv[2] if len(sys.argv)>2 else Path(__file__).resolve().parent.parent/'evidence'/'finite_jacobi_100.json')
src=json.loads(INPUT.read_text())['moments'][:100]
assert len(src)==100 and all(isinstance(x,str) and x.startswith('0.') for x in src)
ctx.dps=460
raw=[arb(t) for t in src]
rho=raw[99]/raw[98]
g=[raw[i]/(raw[0]*rho**i) for i in range(100)]

def interval_ldl(s):
  size=50
  A=[[g[s+i+j] for j in range(size)] for i in range(size)]
  piv=[]
  for k in range(size):
    p=A[k][k]
    if not bool(p>0):
      raise AssertionError(f'INCONCLUSIVE or NONPOSITIVE interval pivot sector {s}, k={k}: {p}')
    piv.append(p)
    if k==size-1:break
    for i in range(k+1,size):
      fac=A[i][k]/p
      for j in range(i,size):
        A[i][j]-=fac*A[k][j]
        if j!=i:A[j][i]=A[i][j]
  return piv
t0=time.time()
p0=interval_ldl(0)
print('ARB PD H0_50: ALL 50 pivots strictly positive; last',p0[-1],flush=True)
p1=interval_ldl(1)
print('ARB PD H1_50: ALL 50 pivots strictly positive; last',p1[-1],flush=True)
print('ARB LDL elapsed',round(time.time()-t0,2),flush=True)

# Second, independent high-precision computation from decimal values;
# no use of eigenvalues, zeta zeros or any fitted spectral parameters.
mp.dps=250
mraw=[mp.mpf(x[:610]) for x in src]
r=mraw[-1]/mraw[-2]
m=[v/(mraw[0]*r**i) for i,v in enumerate(mraw)]
n=50
A=[[m[i+j] for j in range(n)] for i in range(n)]
L=[[mp.mpf(0)]*n for _ in range(n)]
P=[];piv=[];diag=[]
for k in range(n):
  pol=[mp.mpf(0)]*(k+1);pol[k]=1
  for i in range(k):
    fac=L[k][i]
    for j,c in enumerate(P[i]):pol[j]-=fac*c
  P.append(pol)
  pk=A[k][k];piv.append(pk)
  ak=mp.fsum(pol[i]*pol[j]*m[i+j+1]
     for i in range(k+1) for j in range(k+1))/pk
  diag.append(ak)
  if k==n-1:break
  for i in range(k+1,n):L[i][k]=A[i][k]/pk
  for i in range(k+1,n):
    fac=L[i][k]
    for j in range(i,n):
      A[i][j]-=fac*A[k][j]
      if j!=i:A[j][i]=A[i][j]
J=mp.matrix(n)
for k in range(n):
  J[k,k]=diag[k]
  if k:
    J[k,k-1]=J[k-1,k]=mp.sqrt(piv[k]/piv[k-1])
mp.dps=180
evals,V=mp.eigsy(J)
nodes=[evals[i] for i in range(n)]
weights=[V[0,i]**2 for i in range(n)]
assert all(x>0 for x in nodes)
assert all(w>0 for w in weights)
errors=[]
for k in range(100):
  rec=mp.fsum(weights[i]*nodes[i]**k for i in range(n))
  errors.append(abs(rec/m[k]-1))
maxerr=max(errors)
assert maxerr<mp.mpf('1e-140'),str(maxerr)
print('50 positive Jacobi nodes and weights; all 100 moments reconstructed, max relative error',mp.nstr(maxerr,5),flush=True)
print('largest nodes + scaled heights:')
for j in range(6):
  idx=49-j
  print(j+1,mp.nstr(nodes[idx],17),mp.nstr(1/mp.sqrt(r*nodes[idx]),18),
      mp.nstr(weights[idx],17),flush=True)
print('asymptotic rho',mp.nstr(r,20),'first spectral weight',mp.nstr(weights[-1],20),flush=True)
print('elapsed',round(time.time()-t0,2),flush=True)
out=dict(status='FINITE_DECIMAL_DATA_ARB_INTERVAL_POSITIVITY_AND_NUMERIC_GAUSS_QUADRATURE',
  proof_scope='50x50 unshifted and shifted Hankel matrices of stored decimal moments; NOT native all-order',
  source_path=str(INPUT),sha256=hashlib.sha256(INPUT.read_bytes()).hexdigest(),
  input_count=100,interval_dps=460,jacobi_dps=180,
  positive_arb_unshifted_pivots=50,positive_arb_shifted_pivots=50,
  rho=str(r),gamma_approx=str(1/mp.sqrt(r)),
  last_pivot0=str(p0[-1]),last_pivot1=str(p1[-1]),
  largest_modes=[dict(x=str(nodes[-1-j]),weight=str(weights[-1-j]),
      height_scale=str(1/mp.sqrt(r*nodes[-1-j]))) for j in range(10)],
  min_node=str(nodes[0]),max_rel_reconstruction_error=str(maxerr),
  note='Jacobi moment representation exact in finite algebra when H0,H1 are PD; values shown approximate for stored decimals. Finite quadrature does not prove any next pivot or all-order positivity.')
OUTPUT.parent.mkdir(parents=True,exist_ok=True)
OUTPUT.write_text(json.dumps(out,indent=2)+'\n')
print('EVIDENCE_FILE',OUTPUT,flush=True)
