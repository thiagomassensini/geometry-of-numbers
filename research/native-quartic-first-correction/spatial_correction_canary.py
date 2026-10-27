#!/usr/bin/env python3
"""Finite exact-rational tests of an all-order SPATIAL coefficient candidate.

No canonical moments, zeros, heights, theta or fitted coefficients are inputs.
This script is not a Lean proof of the all-order candidate or any positivity.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json


def source(r):
    """Literal even jet profile, including radial phase and (2r)! ."""
    m = 2*r
    return [F((-1)**(r+j)*comb(m, j), factorial(m)) for j in range(m+1)]


def pairing(r, s, p):
    return sum((a*b*F((j+1)**p, i+j+2)
                for i, a in enumerate(source(r))
                for j, b in enumerate(source(s))), F(0))


def first(m):
    return F((m+1)*(m+2), 2)


def second(m):
    return F((m+1)*(m+2)*(m+3)*(3*m+4), 24)


rows = []
for r in range(5):
    for s in range(5):
        m, n = 2*r, 2*s
        phase = (-1)**(r+s)
        lower = []
        for p in range(1, m+n+1, 2):
            value = pairing(r, s, p)+pairing(s, r, p)
            assert value == 0, (r, s, p, value)
            lower.append(p)
        leading = pairing(r, s, m+n+1)+pairing(s, r, m+n+1)
        forward = pairing(r, s, m+n+3)
        reverse = pairing(s, r, m+n+3)
        candidate = phase*(second(m)+second(n)-first(m)*first(n))
        assert leading == phase, (r, s, leading)
        assert forward+reverse == candidate, (r, s, forward, reverse, candidate)
        rows.append({"r": r, "s": s, "canceled_odd_weights": lower,
                     "leading_sum": str(leading), "first_correction_weight": m+n+3,
                     "ordered_forward": str(forward), "ordered_reverse": str(reverse),
                     "candidate_ordered_sum": str(candidate)})

result = {
    "status": "PASS_FINITE_RATIONAL_ONLY",
    "range": "0 <= r,s <= 4",
    "pairs": len(rows),
    "metric": "1/(i+j+2), the original Cauchy feature pairing",
    "source": "(-1)^(r+j) choose(2r,j)/(2r)!",
    "all_order_candidate_proved_in_Lean": False,
    "canonical_positivity_claim": False,
    "rows": rows,
}
root = Path(__file__).resolve().parent
(root/"evidence").mkdir(exist_ok=True)
(root/"evidence/spatial-correction-canary.json").write_text(json.dumps(result, indent=2)+"\n")
print("PASS_FINITE_RATIONAL_ONLY: 25 ordered-pair tests; all-order candidate remains unproved.")
