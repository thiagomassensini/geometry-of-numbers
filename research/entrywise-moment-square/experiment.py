#!/usr/bin/env python3
"""Literal h[n]**2 test. Reuses user decimals; never evaluates zeta or zeros.

Fractions certify only the stored decimals. High-precision eigenvalues remain
numerical diagnostics; NativeWitness.lean handles the actual original source.
"""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import mpmath as mp

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / 'evidence'
EVIDENCE.mkdir(exist_ok=True)


def pivots(h, n, shift):
    a = [[h[i+j+shift] for j in range(n)] for i in range(n)]
    out = []
    for k in range(n):
        pivot = a[k][k]
        assert pivot > 0, ('nonpositive stored-data pivot', n, shift, k)
        out.append(pivot)
        for i in range(k+1, n):
            for j in range(i, n):
                a[i][j] -= a[i][k]*a[k][j]/pivot
                a[j][i] = a[i][j]
    return out


def mpf(q):
    return mp.mpf(q.numerator)/q.denominator


def spectral(h, n, precision):
    with mp.workdps(precision):
        g = mp.matrix([[mpf(h[i+j]) for j in range(n)] for i in range(n)])
        k = mp.matrix([[mpf(h[i+j+1]) for j in range(n)] for i in range(n)])
        lower = mp.cholesky(g)
        b = lower**-1
        j = b*k*b.T
        eig = list(mp.eigsy(j, eigvals_only=True))
        assert all(x > 0 for x in eig)
        err = max(abs((lower*lower.T-g)[i,l]) for i in range(n) for l in range(n))
        return {'eigenvalues_ascending': [mp.nstr(x, 55) for x in eig],
                'heights_ascending': [mp.nstr(x, 55) for x in sorted(1/mp.sqrt(x) for x in eig)],
                'G_LLt_absolute_residual': mp.nstr(err, 8)}


records = []
sources = []
for source_order in (4, 6):
    path = ROOT / 'data' / f'user-N{source_order}.json'
    content = path.read_bytes()
    data = json.loads(content)
    h = [Fraction(s) for s in data['momentos']]
    squared = [x*x for x in h]
    sources.append({'file': str(path.relative_to(ROOT)),
                    'sha256': hashlib.sha256(content).hexdigest(),
                    'stored_moment_count': len(h),
                    'max_significant_digits': 28,
                    'scope': 'exact rationals of stored decimals; not integral enclosures'})
    for n in (1, 2, source_order):
        record = {'source_order': source_order, 'order': n, 'families': {}}
        for name, sequence in [('original_h', h), ('entrywise_square_h', squared)]:
            exact = [pivots(sequence, n, shift) for shift in (0, 1)]
            results = [spectral(sequence, n, dps) for dps in (100, 160)]
            # Same rational inputs at two working precisions. This does not add
            # digits to the 28-significant-digit source checkpoint.
            with mp.workdps(80):
                differences = [abs(mp.mpf(a)-mp.mpf(b))
                               for key in ('eigenvalues_ascending', 'heights_ascending')
                               for a,b in zip(results[0][key], results[1][key])]
                assert max(differences) < mp.mpf('1e-45')
            record['families'][name] = {
                'exact_H_pivots': [str(x) for x in exact[0]],
                'exact_K_pivots': [str(x) for x in exact[1]],
                'spectra': results[1],
                'precision_crosscheck_absolute': str(max(differences))}
        if n == 1:
            eigen = h[1]/h[0]
            assert squared[1]/squared[0] == eigen**2
            assert 0 < eigen < 1
            record['exact_singleton_square_identity'] = True
        records.append(record)
        print(f'PASS stored decimals: source N={source_order}, section N={n}', flush=True)

# Exact rational controls independent of canonical data.
assert 1 - 2*Fraction(2)**2 + 1 == -6
assert all((2**n+3**n)**2 == 4**n+2*6**n+9**n for n in range(9))
output = {'scope': 'FINITE_STORED_DECIMAL_EXPERIMENT_NOT_ALL_ORDER_PROOF',
          'mpmath_version': mp.__version__, 'working_precisions': [100,160],
          'sources': sources, 'records': records,
          'controls': {'negative_squared_hankel_quadratic': '-6',
                       'product_nodes_example': '2,3 -> 4,6,9 (weights 1,2,1)'}}
(EVIDENCE / 'experiment.json').write_text(json.dumps(output, indent=2)+'\n')
print('PASS: exact stored-decimal pivots, singleton identity, spectral precision checks, controls')
