#!/usr/bin/env python3
"""Finite rational probe of the NEXT mixed imaginary coefficient, not a Lean proof.
Only original factorial stencils and the literal Cauchy metric are inputs.
The two ordered kernels remain recorded separately; no moments or heights.
"""
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json


def stencil(m):
    return [F((-1)**(m-i)*comb(m, i), factorial(m)) for i in range(m+1)]


def kernel(m, n, p):
    return sum((x*y*F((j+1)**p, i+j+2)
                for i, x in enumerate(stencil(m))
                for j, y in enumerate(stencil(n))), F(0))


records = []
for r in range(5):
    for s in range(5):
        m, n = 2*r, 2*s+1
        p = m+n+2
        left, right = kernel(m, n, p), kernel(n, m, p)
        expected = F((n+1)*(n+2)-(m+1)*(m+2), 2)
        assert left+right == expected, (r, s, left, right, expected)
        lower = []
        for j in range(r+s+1):
            lo, rev = kernel(m, n, 2*j+1), kernel(n, m, 2*j+1)
            assert lo+rev == 0
            lower.append({"degree": 2*j+1, "left": str(lo), "right": str(rev)})
        records.append({"r": r, "s": s, "degree": p, "left": str(left),
                        "right": str(right), "sum": str(left+right),
                        "candidate": str(expected), "lower_odd_cancellations": lower})
result = {"status": "PASS_FINITE_RATIONAL_ONLY", "pairs": len(records),
          "not_a_proof_of_all_order_rate": True, "records": records}
root = Path(__file__).resolve().parent
(root/"evidence").mkdir(exist_ok=True)
(root/"evidence/mixed-rate-canary.json").write_text(json.dumps(result, indent=2)+"\n")
print("PASS_FINITE_RATIONAL_ONLY: 25 independent-index pairs; two ordered kernels retained.")
