#!/usr/bin/env python3
"""Independent exact-rational regressions of the native finite evaluator.

Theorems are supplied by Lean, including every infinite remainder. This file
does not promote agreement of finite computations to an infinite estimate.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import math
import re
import interval_data as b

root = Path(__file__).resolve().parent


def read_boxes(path, name):
    s = path.read_text()
    match = re.search(r'def '+name+r'[^\n]*:= !\[([^\]]+)\]', s)
    assert match, name
    return [(Q(a), Q(c)) for a, c in re.findall(r'⟨\(([^)]+)\),\(([^)]+)\)⟩', match[1])]


def read_box(path, name):
    match = re.search(r'def '+name+r'[^\n]*:= ⟨\(([^)]+)\),\(([^)]+)\)⟩', path.read_text())
    assert match, name
    return Q(match[1]), Q(match[2])


logs = read_boxes(root/'SamplePrimitiveBoxes.lean', 'sampleLogReference')
amps = read_boxes(root/'SamplePrimitiveBoxes.lean', 'sampleAmplitudeReference')
assert len(logs) == len(amps) == 205
for n in range(1, 206):
    assert logs[n-1] == b.wider(b.log_(Q(n), n.bit_length()))
    assert amps[n-1] == b.wider(b.exp_(b.mul(b.point(Q(-1, 2)), logs[n-1])))

primitive = root/'CompletionPrimitiveBoxes.lean'
pl = read_box(primitive, 'piLogReference')
ea = read_box(primitive, 'piAmplitudeReference')
ca = read_box(primitive, 'chartAmplitudeReference')
pilo = Q(314159265358979323846, 10**20)
pihi = Q(314159265358979323847, 10**20)
assert pl == b.wider((b.log_(pilo, 2)[0], b.log_(pihi, 2)[1]))
assert ea == b.wider(b.exp_(b.mul(b.point(Q(-1, 4)), pl)))
assert ca == b.wider(b.exp_(b.mul(b.point(Q(1, 2)), logs[2])))


def wave(n, r):
    return b.mul(amps[n-1], b.mul(b.pow_(b.neg(logs[n-1]), r), b.point(Q(1, math.factorial(r)))))


weights = [Q(728, 729), Q(-1444, 729), Q(638, 729), Q(364, 243),
           Q(-815, 243), Q(880, 243), Q(-637, 243), Q(329, 243),
           Q(-121, 243), Q(91, 729), Q(-14, 729), Q(1, 729)]
boundary_coefficients = {1: Q(-1, 3), 2: Q(1, 3), 3: Q(-2, 9), 4: Q(1, 9),
                         5: Q(-1, 27), 7: Q(1, 81), 8: Q(-1, 81),
                         9: Q(2, 243), 10: Q(-1, 243), 11: Q(1, 729)}
for k in range(12):
    assert weights[k] == sum((v * (-1)**(j-k)*math.comb(j, k)
                              for j, v in boundary_coefficients.items() if k <= j), Q(0))
# Exact stencil residual: D² = B(D)*(1-(1+D)^3)+D^14/729.
residual = [Q(0)]*15
for j, v in boundary_coefficients.items():
    for shift, c in [(1, -3), (2, -3), (3, -1)]:
        residual[j+shift] += v*c
residual[14] += Q(1, 729)
assert residual == [Q(1) if j == 2 else Q(0) for j in range(15)]


def head(r):
    return b.add(b.add(b.point(1 if r == 0 else 0), b.sum_(
        b.add(b.sub(wave(3*k+2, r), b.mul(b.point(2), wave(3*k+3, r))), wave(3*k+4, r))
        for k in range(64))), b.sum_(b.mul(b.point(v), wave(194+k, r)) for k, v in enumerate(weights)))


heads = read_boxes(root/'HeadEvaluatorData.lean', 'headReferenceBox')
assert heads == [b.wider(head(r), 22) for r in range(7)]
poly = [b.point(Q(-1, 8) if r == 0 else Q(1, 2) if r == 2 else 0) for r in range(7)]
expo = [b.mul(ea, b.mul(b.pow_(b.mul(b.point(Q(-1, 2)), pl), r),
                       b.point(Q(1, math.factorial(r))))) for r in range(7)]
chart = [b.sub(b.point(1 if r == 0 else 0), b.mul(ca, b.mul(b.pow_(b.neg(logs[2]), r),
                       b.point(Q(1, math.factorial(r)))))) for r in range(7)]
inverse = []
for n in range(7):
    inverse.append(b.inv(chart[0]) if n == 0 else b.mul(b.neg(b.sum_(
        b.mul(inverse[j], chart[n-j]) for j in range(n))), b.inv(chart[0])))


def conv(a, c):
    return [b.sum_(b.mul(a[j], c[r-j]) for j in range(r+1)) for r in range(7)]


left = conv(conv(conv(poly, expo), inverse), heads)
gfile = root.parent/'c3-gamma-jet-enclosures/LogGammaData.lean'
gmatch = re.search(r'def gammaRealReference[^\n]*:= !\[([^\]]+)\]', gfile.read_text())
gamma = list(map(Q, gmatch[1].split(',')))
full = conv(left, [b.point(q) for q in gamma])
references = [Q(497120778188314, 10**15), Q(-11485972157573, 10**15),
              Q(123452018070, 10**15), Q(-832355481, 10**15)]
rows = []
for j, ref in enumerate(references):
    a = full[2*j] if j % 2 == 0 else b.neg(full[2*j])
    assert ref-Q(1, 10**13) <= a[0] <= a[1] <= ref+Q(1, 10**13)
    rows.append({'order': 2*j, 'rational_box': [str(x) for x in a],
                 'max_reference_distance': str(max(abs(a[0]-ref), abs(a[1]-ref)))})

# Analytic remainders are independently proved in Lean; check their rational
# combination at all seven orders without replacing either infinite source.
budgets = []
for r in range(7):
    tail = Q(96*math.factorial(14)*4**r, 729*191**13)
    gamma_error = Q(64*sum(4**j for j in range(r+1)), 10**18)
    assert tail+gamma_error <= Q(4, 10**13)
    assert tail+gamma_error+Q(1, 10**13) <= Q(1, 10**12)
    budgets.append({'order': r, 'tail_bound': str(tail), 'gamma_bound': str(gamma_error)})

result = {'status': 'PASS_EXACT_RATIONAL_REGRESSION', 'rows': rows,
          'combined_analytic_budgets': budgets, 'source_box_claim_requires_Lean_build': True,
          'uses_mpmath_theta_zeros_heights_or_moment_checkpoints': False,
          'all_order_positivity': False}
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/exact-interval-regression.json').write_text(json.dumps(result, indent=2)+'\n')
print('PASS: all native finite interval witnesses, original C3 stencil and seven rational error budgets')
