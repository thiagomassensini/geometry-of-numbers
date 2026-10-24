#!/usr/bin/env python3
"""Replay the published numerical example and check its DECIMAL references
independently with Fraction and direct Hankel solves. Not an integral or
all-order positivity certificate. The Momentos checkout is never edited.
"""
from pathlib import Path
from fractions import Fraction as Q
import csv
import hashlib
import json
import os
import subprocess

root = Path(__file__).resolve().parent
target = root / '.cache/momentos-0d0dd09'
target.mkdir(parents=True, exist_ok=True)
evidence = root / 'evidence'
evidence.mkdir(exist_ok=True)
commit = '0d0dd0975a1558ced731e9246c14420c0e0720f4'
source = 'investigations/jacobi_polynomial_moments_20261024'
names = ['derivacao_jacobi_momentos_c2.md', 'jacobi_polynomial_series.py',
         'c2_momentos_16_excerpt.csv']
digests = {}
for name in names:
    data = subprocess.check_output(['gh', 'api',
        f'repos/thiagomassensini/momentos/contents/{source}/{name}?ref={commit}',
        '-H', 'Accept: application/vnd.github.raw+json'])
    (target/name).write_bytes(data)
    digests[name] = hashlib.sha256(data).hexdigest()
python = os.environ.get('MOMENTOS_PYTHON', '/home/thlinux/miniforge3/bin/python')
with (evidence/'momentos-n8-d100.log').open('w') as log:
    subprocess.run([python, str(target/'jacobi_polynomial_series.py'),
                    '--order', '8', '--digits', '100'], check=True,
                   stdout=log, stderr=subprocess.STDOUT)

rows = list(csv.DictReader((target/names[2]).open()))
assert [int(r['k']) for r in rows] == list(range(16))
h = [Q(r['h_k']) for r in rows]

def solve(a, b):
    """Exact elimination of the moment equations, without polynomial recurrence."""
    n = len(b)
    a = [list(row)+[b[i]] for i, row in enumerate(a)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        q = a[j][j]
        a[j] = [x/q for x in a[j]]
        for i in range(n):
            if i != j:
                q = a[i][j]
                a[i] = [x-q*y for x, y in zip(a[i], a[j])]
    return [row[-1] for row in a]

def pairing(p, q, shift=0):
    return sum((x*y*h[i+j+shift] for i,x in enumerate(p)
                for j,y in enumerate(q)), Q(0))

polys = [[Q(1)]]
for n in range(1, 9):
    polys.append(solve([[h[i+j] for j in range(n)] for i in range(n)],
                       [-h[n+i] for i in range(n)])+[Q(1)])
norms = [pairing(p,p) for p in polys[:8]]
assert all(q > 0 for q in norms)
alpha = [pairing(p,p,1)/q for p,q in zip(polys,norms)]
beta = [Q(0)]+[norms[n]/norms[n-1] for n in range(1,8)]

for n in range(8):
    successor = [Q(0)]+polys[n]
    for j,c in enumerate(polys[n]): successor[j] -= alpha[n]*c
    if n:
        for j,c in enumerate(polys[n-1]): successor[j] -= beta[n]*c
    assert successor == polys[n+1]

def powers(n, count):
    """Monic multiplication matrix: lower diagonal 1, upper diagonal beta.
    No square roots and no symmetric-Jacobi positivity premise are used here.
    """
    v = [Q(1)]+[Q(0)]*(n-1)
    out = []
    for _ in range(count):
        out.append(h[0]*v[0])
        v = [alpha[i]*v[i] + (v[i-1] if i else 0) +
             (beta[i+1]*v[i+1] if i+1 < n else 0) for i in range(n)]
    return out

prefixes = 0
for n in range(1,9):
    vals = powers(n,2*n+2 if n<8 else 16)
    assert vals[:2*n] == h[:2*n]
    prefixes += 2*n
    if n < 8:
        assert h[2*n]-vals[2*n] == norms[n]
        assert h[2*n+1]-vals[2*n+1] == norms[n]*(alpha[n]+2*sum(alpha[:n]))

result = {'repository':'thiagomassensini/momentos', 'commit':commit,
          'source':source, 'input_sha256':digests,
          'numerical_command':[python,'jacobi_polynomial_series.py','--order','8','--digits','100'],
          'exact_arithmetic':'fractions.Fraction; stored decimals treated as exact rationals',
          'polynomials_from':'direct Hankel solves, independently of the three-term recurrence',
          'positive_reference_pivots':8, 'exact_reconstruction_equalities':prefixes,
          'exact_even_first_missing_equalities':7, 'exact_odd_first_missing_equalities':7,
          'exact_three_term_equalities':8,
          'pivot_fraction_sha256':[hashlib.sha256(str(q).encode()).hexdigest() for q in norms],
          'canonical_integral_certification':False, 'all_order_positivity':False,
          'source_geometry_or_metric_modified':False}
(evidence/'momentos-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: published N8/100-DPS replay and independent exact rational prefix/boundary identities.')
