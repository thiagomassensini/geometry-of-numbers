#!/usr/bin/env python3
"""Audit supplied decimals exactly; optionally reproduce floating source evaluation.

Does not modify attachments or call their test() function (hard-coded output path).
Exact rational checks apply ONLY to the saved finite decimal data, not the source.
"""
import argparse
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
from time import perf_counter

import mpmath as mp

BASE = Path(__file__).resolve().parent / 'fixtures'
OUT = Path(__file__).resolve().parent / 'evidence'
OUT.mkdir(exist_ok=True)


def exact_ldl(A):
    n = len(A)
    assert all(A[i][j] == A[j][i] for i in range(n) for j in range(n))
    L = [[Fraction(i == j) for j in range(n)] for i in range(n)]
    d = []
    for j in range(n):
        pivot = A[j][j] - sum(L[j][k] ** 2 * d[k] for k in range(j))
        assert pivot > 0, (j, pivot)
        d.append(pivot)
        for i in range(j + 1, n):
            L[i][j] = (A[i][j] - sum(L[i][k] * d[k] * L[j][k]
                                     for k in range(j))) / pivot
    assert all(A[i][j] == sum(L[i][k] * d[k] * L[j][k]
                             for k in range(n))
               for i in range(n) for j in range(n))
    return {'positive_pivots': True, 'exact_reconstruction': True,
            'pivots_rational': [str(x) for x in d],
            'pivots_approx': [mp.nstr(mp.mpf(x.numerator) / x.denominator, 22)
                              for x in d]}


def maxabs(A):
    return max(abs(x) for x in A)


def number(x):
    return mp.nstr(x, 24)


def saved_audit(data):
    result = {}
    for N in (4, 6):
        item = data[N]
        h = [Fraction(x) for x in item['momentos']]
        result[str(N)] = {}
        for key, shift in (('G', 0), ('K', 1)):
            A = [[Fraction(x) for x in row] for row in item['matrizes'][key]]
            assert all(A[i][j] == A[p][q]
                       for i in range(N) for j in range(N)
                       for p in range(N) for q in range(N) if i+j == p+q)
            result[str(N)][key + '_48_digit_matrix'] = exact_ldl(A)
            H = [[h[i+j+shift] for j in range(N)] for i in range(N)]
            result[str(N)][key + '_28_digit_moments'] = exact_ldl(H)
        a = {k: mp.matrix(v) for k, v in item['matrizes'].items()}
        result[str(N)]['residual_using_saved_L'] = number(maxabs(a['G']-a['L']*a['L'].T))
        result[str(N)]['residual_using_saved_T_J'] = number(maxabs(a['T']*a['J']*a['T']-mp.eye(N)))
        x = mp.matrix(item['sos']['x'])
        result[str(N)]['quadratic_using_saved_G'] = number((x.T*a['G']*x)[0])
    prefix = {}
    for key in ('G', 'K', 'L', 'J', 'T'):
        a, b = [mp.matrix(data[N]['matrizes'][key]) for N in (4, 6)]
        prefix[key + '_max_abs_difference'] = number(max(
            abs(a[i,j]-b[i,j]) for i in range(4) for j in range(4)))
    result['prefix_N4_in_N6'] = prefix
    return result


def reproduce(data):
    path = BASE / 'operador_finito_canonico.py'
    spec = importlib.util.spec_from_file_location('supplied_finite_operator', path)
    supplied = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(supplied)
    result = {}
    for N, dps, nodes, check_nodes in ((4,105,224,280), (6,125,260,320)):
        print(f'Reproducing N={N}, dps={dps}, nodes={nodes}/{check_nodes}', flush=True)
        start = perf_counter()
        mp.mp.dps = dps
        h = supplied.canonical_moments(supplied.cauchy_even_coefficients(2*N+1,nodes,mp.mpf(3)))
        hc = supplied.canonical_moments(supplied.cauchy_even_coefficients(2*N+1,check_nodes,mp.mpf(4)))
        G, K = supplied.hankel(h,N), supplied.hankel(h,N,1)
        L, Lk = mp.cholesky(G), mp.cholesky(K)
        B = L**-1
        J = B*K*B.T
        eig, U = mp.eigsy(J)
        assert min(eig) > 0
        heights = [eig[i]**(-mp.mpf('0.5')) for i in range(N)]
        T = U*mp.diag(heights)*U.T
        old = data[N]
        moment_error = max(abs((h[i]-mp.mpf(old['momentos'][i]))/h[i]) for i in range(2*N))
        assert moment_error < mp.mpf('1e-27')
        errors = {key: maxabs(A-mp.matrix(old['matrizes'][key]))
                  for key,A in (('G',G),('K',K),('L',L),('J',J),('T',T))}
        assert max(errors.values()) < mp.mpf('1e-44')
        result[str(N)] = {
            'dps':dps, 'nodes':nodes, 'check_nodes':check_nodes,
            'radii':['3','4'], 'elapsed_seconds':perf_counter()-start,
            'moments_relative_error_against_28_digit_saved':number(moment_error),
            'same_algorithm_radius_node_crosscheck_relative':number(max(abs((h[i]-hc[i])/h[i]) for i in range(2*N))),
            'matrix_max_abs_error_against_48_digit_saved':{k:number(v) for k,v in errors.items()},
            'pivots_G':[number(L[i,i]**2) for i in range(N)],
            'pivots_K':[number(Lk[i,i]**2) for i in range(N)],
            'heights_ascending':[number(x) for x in sorted(heights)],
            'G_LLt_residual':number(maxabs(G-L*L.T)),
            'J_nontridiagonal_residual':number(max(abs(J[i,j]) for i in range(N) for j in range(N) if abs(i-j)>1)),
            'TJT_residual':number(maxabs(T*J*T-mp.eye(N))),
            'status':'FLOATING_POINT_REPRODUCTION_NOT_SOURCE_ERROR_BOUND'}
        print(f'N={N} reproduced in {perf_counter()-start:.1f}s', flush=True)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--reproduce-source', action='store_true')
    args = parser.parse_args()
    mp.mp.dps = 160
    paths = [BASE / name for name in (
        'operador_finito_canonico.py','operador_finito_canonico_N4.json',
        'operador_finito_canonico_N6.json','relatorio_operador_finito_canonico.md')]
    data = {N:json.loads((BASE/f'operador_finito_canonico_N{N}.json').read_text()) for N in (4,6)}
    report = {'scope':'EXACT_FINITE_DECIMALS_AND_FLOATING_REPRODUCTION_NOT_LEAN_OR_ALL_ORDER',
              'python':platform.python_version(), 'mpmath':mp.__version__,
              'sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'saved_data':saved_audit(data)}
    if args.reproduce_source:
        report['source_reproduction'] = reproduce(data)
    target = OUT/('audit-full.json' if args.reproduce_source else 'audit-saved.json')
    target.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print(target)


if __name__ == '__main__':
    main()
