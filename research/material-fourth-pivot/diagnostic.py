"""Replay the unchanged native theta -> characteristic -> moment -> pivot chain.

Decimal arithmetic and preserved caches are diagnostic only. No cache value
or numerical result is imported into a Lean proof.
"""
import decimal
import hashlib
import json
from math import factorial
from pathlib import Path
import sys

CACHE = Path('/home/thlinux/.native_height_cache/theta-even-moments-v1-dps1600.json')
MOMENTS = Path('/home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_B/coefficients.json')
OUT = Path(sys.argv[1])
D = decimal.Decimal
cache = json.loads(CACHE.read_text())
reference = json.loads(MOMENTS.read_text())['canonical_h']
records = []
for precision in [100, 180]:
    decimal.getcontext().prec = precision
    # The cache uses log(x); Lean's theta-tail coordinate is log(x)/2.
    # Its even moment index k therefore carries the literal factor 4^k.
    A = [D(cache['moments'][str(k)])/D(4**k) for k in range(10)]
    c = [D('0.5')-A[0]/4]+[
        (-1)**n*(A[n-1]/D(factorial(2*n-2))-A[n]/(4*D(factorial(2*n))))
        for n in range(1, 10)]
    h = []
    for n in range(9):
        h.append((-(n+1)*c[n+1]-sum((h[k]*c[n-k] for k in range(n)), D(0)))/c[0])
    R = [[h[i+j+2]-h[i+1]*h[j+1]/h[0] for j in range(4)] for i in range(4)]
    pivots = []
    columns = []
    for r in range(4):
        pivot = R[r][r]
        pivots.append(pivot)
        columns.append([R[i][r]/pivot for i in range(4)])
        R = [[R[i][j]-R[i][r]*R[r][j]/pivot for j in range(4)] for i in range(4)]
    # Back substitution cancels the three extracted source columns.
    x = [D(0), D(0), D(0), D(1)]
    for r in [2, 1, 0]:
        x[r] = -sum((columns[r][i]*x[i] for i in range(r+1, 4)), D(0))
    K = [[h[i+j+2]-h[i+1]*h[j+1]/h[0] for j in range(4)] for i in range(4)]
    critical_energy = sum((K[i][j]*x[i]*x[j] for i in range(4) for j in range(4)), D(0))
    threshold = h[8]-pivots[3]
    ceiling = -(sum((h[k]*c[8-k] for k in range(8)), D(0))+c[0]*threshold)/9
    theta_balance = 1224*A[8]-A[9]
    theta_required = -4*D(factorial(18))*ceiling
    max_rel_error = max(abs(h[k]-D(reference[k]))/abs(D(reference[k])) for k in range(9))
    assert max_rel_error < D(10)**(-(precision-12))
    assert abs((critical_energy-pivots[3])/pivots[3]) < D(10)**(-(precision-18))
    assert abs((ceiling-c[9])-c[0]*pivots[3]/9) < D(10)**(-(precision-10))
    fmt = lambda x: format(x, '.65E')
    records.append(dict(precision=precision, native_moments=[fmt(x) for x in h],
        material_pivots=[fmt(x) for x in pivots], threshold=fmt(threshold),
        c9=fmt(c[9]), c9_ceiling=fmt(ceiling), c9_gap=fmt(ceiling-c[9]),
        theta16=fmt(A[8]), theta18=fmt(A[9]), theta_balance=fmt(theta_balance),
        theta_required=fmt(theta_required), theta_gap=fmt(theta_balance-theta_required),
        critical_vector=[fmt(t) for t in x], critical_energy=fmt(critical_energy),
        relative_reference_error=fmt(max_rel_error)))
record = dict(status='NUMERICAL_DIAGNOSTIC_ONLY_NOT_A_SOURCE_INTERVAL_CERTIFICATE',
    source_changed=False, new_quadrature=False, zeros_or_heights_used=False,
    cache=dict(path=str(CACHE), sha256=hashlib.sha256(CACHE.read_bytes()).hexdigest(),
               recorded_dps=cache['dps'], coordinate_conversion='A[2k] = cached[k] / 4^k'),
    moments=dict(path=str(MOMENTS), sha256=hashlib.sha256(MOMENTS.read_bytes()).hexdigest()),
    runs=records)
OUT.write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({k: records[-1][k] for k in
                 ['material_pivots', 'c9', 'c9_ceiling', 'c9_gap', 'theta_gap', 'critical_energy']}, indent=2))
