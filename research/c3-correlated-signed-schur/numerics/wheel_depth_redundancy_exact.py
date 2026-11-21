#!/usr/bin/env python3
"""Exact finite conditional expectations for 'already resolved' cameras.

Prime camera 2 complete = full 2-adic depth up to resolution K.
Shallow camera 2 = parity only. Test how innovation depends on this
distinction, and that a new prime-3 wheel still gives independent data.
No completion, native Hankel positivity, or zero data used.
"""
from fractions import Fraction as Q
from pathlib import Path
from json import dumps

def depth2_truncated(n,K):
  if n==0:return K
  k=0
  while k<K and n%2==0:
    n//=2;k+=1
  return k

def residual_energy(f,groups):
  N=len(f)
  proj={}
  for key in set(groups):
    idx=[i for i,key2 in enumerate(groups) if key2==key]
    proj[key]=sum((f[i] for i in idx),Q(0))/len(idx)
  residual=[f[i]-proj[groups[i]] for i in range(N)]
  return sum((v*v for v in residual),Q(0))/N, proj

rows=[]
for K in range(2,8):
  N=3*(2**K)
  c4=[Q(int(n%4==0)) for n in range(N)]
  c3=[Q(int(n%3==0)) for n in range(N)]
  parity=[n%2 for n in range(N)]
  depth=[depth2_truncated(n,K) for n in range(N)]
  shallow,_=residual_energy(c4,parity)
  deep,_=residual_energy(c4,depth)
  new_prime,_=residual_energy(c3,depth)
  assert shallow==Q(1,8)
  assert deep==0
  assert new_prime==Q(2,9)
  print(f'K={K}, wheel={N}: 4 after parity={shallow}; 4 after full v2={deep}; 3 after full v2={new_prime}')
  rows.append(dict(depth_resolution=K,period=N,composite4_after_parity=str(shallow),
                   composite4_after_complete_dyadic_depth=str(deep),
                   newprime3_after_complete_dyadic_depth=str(new_prime)))

# Composite 6 is not a new arithmetic camera when the old algebra
# is closed under products of indicators of 2 and 3.
N=6
C2=[int(i%2==0) for i in range(N)]
C3=[int(i%3==0) for i in range(N)]
C6=[int(i%6==0) for i in range(N)]
assert C6==[a*b for a,b in zip(C2,C3)]
print('I_6=I_2*I_3 exactly, though I_6 need not be in the LINEAR span of I_2,I_3')
o=Path(__file__).resolve().parent.parent/'evidence'/'wheel_depth_redundancy_exact.json'
o.write_text(dumps(dict(status='EXACT_RATIONAL_TEST_NOT_NATIVE_POSITIVITY',
                         description='Conditional expectation in finite periodic L2; camera2 interpreted as full dyadic depth.',
                         tests=rows,composite6_indicator_is_product_of_prime2_and_prime3=True),indent=2)+'\n')
print('EVIDENCE',o)
