#!/usr/bin/env python3
"""Exact rational test of prime-wheel LSB innovation vs Schur residual.

This is the sieve/wheel L2 module, NOT a numerical certificate about
the completed native height-moment Hankel matrix.
No zeta, zeros or arbitrary precision settings are used.
"""
from fractions import Fraction as Q
from math import prod
from json import dumps
from pathlib import Path

primes=[2,3,5,7]
rows=[]
for index,p in enumerate(primes):
    W=prod(primes[:index])
    P=W*p
    g=[Q(int(n%p==0))-Q(1,p) for n in range(P)]
    energy=sum(v*v for v in g)/P
    cov=[]
    for q in primes[:index]:
        covq=sum(g[n]*int(n%q==0) for n in range(P))/P
        cov.append([q,str(covq)])
        assert covq==0
    assert energy==Q(p-1,p*p)
    rows.append(dict(old_primorial=W,new_prime=p,period=P,
                     wheel_residual_norm_squared=str(energy),
                     old_camera_covariances=cov))
    print(f'W={W}, p={p}: orthogonal innovation norm²={energy}, old overlaps={cov}')

# Distinguish new directional information from prime birth:
# after wheel 2, the new camera 4 resolves depth among even integers.
v4=[Q(int(n%4==0))-Q(int(n%2==0),2) for n in range(4)]
q4=sum(x*x for x in v4)/4
assert q4==Q(1,8)
print('W=2, camera=4 (composite): new depth direction norm²=',q4)

# Nonnegative individual moments plus infinitely many (other) directions
# do NOT force Hankel PSD. Negative coefficient illustrates sign risk.
h=lambda n: Q(1)+Q(1,2**n)-Q(1,3**n)
det2=h(0)*h(2)-h(1)**2
assert det2==Q(-2,9) and all(h(n)>0 for n in range(30))
print('positive individual moments, signed 2x2 Hankel det=',det2)
print('h0,h1,h2=',*[str(h(n)) for n in range(3)])

dest=Path(__file__).resolve().parent.parent/'evidence'/'wheel_prime_schur_exact.json'
dest.write_text(dumps(dict(status='EXACT_RATIONAL_WHEEL_L2_NOT_NATIVE_MOMENT_PROOF',
   wheel_prime_rows=rows,composite_4_fresh_direction_norm_squared=str(q4),
   positive_moment_counterexample=dict(expression='h_n=1+2^(-n)-3^(-n)',
      first_three=[str(h(n)) for n in range(3)],negative_det_2x2=str(det2)),
   conclusion='A new independent prime-wheel direction gives a strictly positive WHEEL Gram pivot; a positivity-preserving identification with the completed-native moment Gram remains open.'),indent=2)+'\n')
print('EVIDENCE',dest)
