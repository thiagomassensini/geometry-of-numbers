#!/usr/bin/env python3
"""Regenerate only the rational derivative table; Lean checks its correctness."""
from fractions import Fraction as F
from pathlib import Path
import argparse
parser=argparse.ArgumentParser()
parser.add_argument('--out',type=Path,default=Path(__file__).with_name('CoefficientData.lean'))
args=parser.parse_args()
rows=[[F(1)]]
for _ in range(16):
    a=rows[-1];b=[F(0)]*(len(a)+1)
    for j,v in enumerate(a):
        b[j]+=(F(1,2)+2*j)*v
        b[j+1]-=2*v
    rows.append(b)
q=lambda v:f'({v.numerator}/{v.denominator}:ℚ)'
text='import ThetaDerivatives\n\n/-! Exact rational derivative coefficients. The finite table is a cache of\nan algebraic recurrence, checked below against the analytical polynomial. -/\nnamespace CarryIntegralCertificate\nopen Polynomial Real\nset_option autoImplicit false\nset_option maxHeartbeats 4000000\n\ndef thetaCoefficientCode : ℕ → List ℚ\n'
for n,a in enumerate(rows):text+=f'  | {n} => ['+','.join(map(q,a))+']\n'
text+='  | _ => []\n\nnoncomputable def thetaPolynomialCode (n : ℕ) : Polynomial ℚ :=\n  ∑ r ∈ Finset.range (n+1), C ((thetaCoefficientCode n)[r]?.getD 0)*X^r\n\nend CarryIntegralCertificate\n'
args.out.write_text(text)
