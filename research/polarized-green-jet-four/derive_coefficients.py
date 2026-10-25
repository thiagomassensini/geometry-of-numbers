#!/usr/bin/env python3
"""Exact symbolic identities; no numerical moment, zero or height input."""
from pathlib import Path
import json
import sympy as s
K=s.symbols('K',real=True)
u=s.symbols('u0:3');v=s.symbols('v0:3');h=s.symbols('h0:7')
def weights(u):return [u[0]-u[1]*K**2/2+u[2]*K**4/24,u[1]*K**2-u[2]*K**4/6,-u[1]*K**2/2+u[2]*K**4/4,-u[2]*K**4/6,u[2]*K**4/24]
x,y=weights(u),weights(v)
M=[s.expand(K*(x[j]*sum(y[i]/s.Integer(i+j+2) for i in range(5))+y[j]*sum(x[i]/s.Integer(i+j+2) for i in range(5)))) for j in range(5)]
E=s.expand(sum(M[j]*sum((-1)**n*h[n]*s.Integer(j+1)**(2*n+1)/K**(2*n+1) for n in range(7)) for j in range(5)))
expected=sum(u[i]*v[j]*h[i+j] for i in range(3) for j in range(3))
assert s.expand(E.coeff(K,0)-expected)==0
assert all(E.coeff(K,n)==0 for n in [2,4,6,8])
for degree in [0,-2,-4,-6,-8,-10,-12]:print('K^'+str(degree),s.factor(E.coeff(K,degree)))
result={'status':'EXACT_SYMBOLIC_CHECK_NOT_LEAN_CERTIFICATE','samples':[str(x) for x in M],
 'coefficients':{str(d):str(E.coeff(K,d)) for d in [0,-2,-4,-6,-8,-10,-12]}}
r=Path(__file__).resolve().parent/'evidence';r.mkdir(exist_ok=True)
(r/'symbolic-coefficients.json').write_text(json.dumps(result,indent=2)+'\n')

# Finite rational canary for the NEXT obligation; not an all-order theorem.
from fractions import Fraction
from math import comb,factorial
B=lambda n:Fraction((n+1)*(n+2),2)
A=lambda n:Fraction((n+1)*(n+2)*(3*n+4)*(n+3),24)
canary=[]
for i in range(5):
    row=[]
    for j in range(5):
        p,q=2*i,2*j
        weight=sum(Fraction((-1)**(r+s)*comb(p,r)*comb(q,s)*
          ((r+1)**(p+q+3)+(s+1)**(p+q+3)),r+s+2)
          for r in range(p+1) for s in range(q+1))/factorial(p)/factorial(q)
        assert weight==A(p)+A(q)-B(p)*B(q)
        row.append(str(weight))
    canary.append(row)
result['next_coefficient_law_canary']={'status':'FINITE_EXACT_CHECK_NOT_ALL_ORDER_PROOF',
 'indices':'0 <= i,j <= 4','weights':canary}
(r/'symbolic-coefficients.json').write_text(json.dumps(result,indent=2)+'\n')
print('NEXT-TARGET CANARY PASS: 25 finite rational weight identities; no moment inputs.')
