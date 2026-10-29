#!/usr/bin/env python3
"""Independent exact regeneration of the finite Gamma witness data.

This script is a regression. The mathematical inclusions are checked separately
by Lean; no Python result is imported as an axiom or a theorem.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import math
import re

root = Path(__file__).resolve().parent


def floors(q, digits):
    scale = 10**digits
    return Q(q.numerator * scale // q.denominator, scale)


def table(path, name):
    text = path.read_text()
    match = re.search(r'def ' + name + r'[^\n]*:= !\[([^\]]+)\]', text)
    assert match, (path, name)
    return [Q(x.strip()) for x in match[1].split(',')]


coefficients = [sum((Q((-81)**k, math.factorial(k)) *
                     Q(4, 4*k+1)**(r+1) for k in range(512)), Q(0))
                for r in range(7)]
references = [floors(q, 32) for q in coefficients]
assert references == table(root/'RationalGammaData.lean', 'coefficientReference')
assert all(abs(a-b) <= Q(1, 10**30) for a, b in zip(coefficients, references))
assert all(abs(a) <= 20000 for a in references)

log_sum = sum((Q(2, 3)**(k+1)/Q(k+1) for k in range(256)), Q(0))
log_reference = floors(log_sum, 32)
log_text = (root/'LogGammaData.lean').read_text()
actual_log_reference = Q(re.search(r'def logReference : ℚ := ([^\n]+)', log_text)[1])
assert log_reference == actual_log_reference
assert abs(log_sum-log_reference) <= Q(1, 10**32)
assert Q(2, 3)**257 / (1-Q(2, 3)) + Q(1, 10**32) <= Q(1, 10**30)

gamma_polynomial = [3*sum(((2*log_reference)**j/Q(math.factorial(j)) *
                          Q(-1, 2)**(r-j)*references[r-j]
                          for j in range(r+1)), Q(0)) for r in range(7)]
gamma_references = [floors(q, 25) for q in gamma_polynomial]
assert gamma_references == table(root/'LogGammaData.lean', 'gammaRealReference')
assert all(abs(a-b) <= Q(1, 10**25) for a, b in zip(gamma_polynomial, gamma_references))

compact_bound = Q(16*81**513, math.factorial(512))
exp_bound = Q(3, 8)**81
assert compact_bound <= Q(1, 10**100)
assert exp_bound <= Q(1, 10**33)
assert compact_bound+exp_bound <= Q(1, 10**32)
assert Q(4**6, 10**32) + Q(10**11, 10**30) + Q(1, 10**25) <= Q(1, 10**18)

result = {
    'status': 'PASS_EXACT_RATIONAL_REGRESSION',
    'proof_engine': 'Python Fraction regression; Lean is audited separately',
    'euler_cutoff': 81,
    'exp_polynomial_terms': 512,
    'coefficient_reference': list(map(str, references)),
    'log_three_reference': str(log_reference),
    'gamma_real_reference': list(map(str, gamma_references)),
    'gamma_reference_complex_phase': 'I^r times the real rational reference',
    'uniform_gamma_error': '1/10^32',
    'seven_gamma_jet_absolute_error': '1/10^18',
    'native_four_F_boxes_discharged': False,
    'canonical_hankel_sign_proved_here': False,
    'all_order_positivity_proved_here': False,
}
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/rational-regression.json').write_text(json.dumps(result, indent=2)+'\n')
print('PASS: seven rational Gamma coefficients, log enclosure, remainder budgets')
