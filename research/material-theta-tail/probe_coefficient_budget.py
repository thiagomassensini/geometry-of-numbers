"""Finite, non-rigorous diagnostic; no roots or target Gram are used.

The moment coefficients already stored by momentos are read without mutation.
The source polynomial and absolute coefficient budget are reconstructed by the
literal recurrence. This does not certify their signs at any infinite order.
"""
import hashlib
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 1100
path = Path('/home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_B/coefficients.json')
data = json.loads(path.read_text())
c = list(map(mp.mpf, data['normalized_completed_c']))
h = list(map(mp.mpf, data['canonical_h']))
# Work with c0*P_n and mu_j/c0: the two ORIGINAL normalization factors
# cancel in the integral. No physical source is rescaled or replaced.
polys = []
rows = []
for n in range(len(h)):
    p = [mp.mpf(0)] * (n+2)
    p[n+1] = (-1)**n * mp.mpf(n+1)/mp.factorial(2*n+2)
    for k in range(n):
        for j, coeff in enumerate(polys[k]):
            p[j] -= c[n-k] * coeff
    polys.append(p)
    if not n:
        continue
    q = p[:]
    if n % 2 == 0:
        s = n//2
        a = h[s]/h[0]
        for j, coeff in enumerate(polys[s]):
            q[j] -= 2*a*coeff
        for j, coeff in enumerate(polys[0]):
            q[j] += a*a*coeff
    raw_moments = [(-1)**j * mp.factorial(2*j)*c[j] for j in range(len(q))]
    budget = mp.fsum(abs(x)*m for x, m in zip(q, raw_moments))
    source_readout = mp.fsum(x*m for x, m in zip(q, raw_moments))
    target = h[n] if n % 2 else h[n] - h[n//2]**2/h[0]
    cutoff = n+2
    modal_error_bound = mp.mpf(128)/63 * mp.exp(-3*cutoff**2-2*cutoff) * budget
    fixed_three_bound = mp.mpf(128)/63 * mp.exp(-33) * budget
    rows.append({
        'order': n,
        'preset_K': cutoff,
        'coefficient_budget': mp.nstr(budget, 35),
        'canonical_C': mp.nstr(target, 35),
        'readout_relative_difference': mp.nstr(abs(source_readout-target)/abs(target), 8),
        'bound_over_abs_C': mp.nstr(modal_error_bound/abs(target), 35),
        'fixed_three_bound_over_abs_C': mp.nstr(fixed_three_bound/abs(target), 35),
        'coefficient_budget_over_abs_C': mp.nstr(budget/abs(target), 35),
        'C_positive_numerically': bool(target > 0),
    })
ratios = [(mp.mpf(row['bound_over_abs_C']), row['order']) for row in rows]
fixed_ratios = [(mp.mpf(row['fixed_three_bound_over_abs_C']), row['order']) for row in rows]
print(json.dumps({
    'status': 'finite_nonrigorous_diagnostic',
    'input_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
    'working_decimal_digits': mp.mp.dps,
    'order_range': [1, len(h)-1],
    'K_rule': 'k+2, chosen before reading signs or ratios',
    'maximum_bound_over_abs_C': {'value': mp.nstr(max(ratios)[0], 35), 'order': max(ratios)[1]},
    'minimum_bound_over_abs_C': {'value': mp.nstr(min(ratios)[0], 35), 'order': min(ratios)[1]},
    'fixed_three_maximum_bound_over_abs_C': {'value': mp.nstr(max(fixed_ratios)[0], 35), 'order': max(fixed_ratios)[1]},
    'rows': rows,
}, indent=2))
