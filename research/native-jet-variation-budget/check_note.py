#!/usr/bin/env python3
"""Exact arithmetic checks for the attached note; not a Lean proof."""
from fractions import Fraction as F
from math import comb, factorial

def moment(j):
    return F(1,100)**(j+1)+F(1,1000)*F(1,10)**(j+1)
def amplitude(m):
    return F((m+1)*(m+2),2)
def variance(m):
    return F((m+1)*(m+2)*(2*m+3),12)
def lam(m,n):
    return variance(m)+variance(n)+F(1,2)*(amplitude(m)-amplitude(n))**2
expected={(1,1):10,(1,3):84,(3,3):60,(1,5):420,(3,5):242,(5,5):182}
for pair,value in expected.items():
    assert 2*lam(*pair)==value,(pair,2*lam(*pair))
def stencil_layer(m,n,d):
    return sum((F((-1)**(m+n-i-j)*comb(m,i)*comb(n,j)*
        ((i+1)**d+(j+1)**d),i+j+2)
        for i in range(m+1) for j in range(n+1)),F())/factorial(m)/factorial(n)

# Direct finite rational control of the original signed binomial stencil and
# the original Cauchy denominator. This is not a proof for arbitrary order.
for m in range(1,16,2):
    for n in range(1,16,2):
        assert stencil_layer(m,n,m+n+1)==-1,(m,n)
        assert stencil_layer(m,n,m+n+3)==-lam(m,n),(m,n)

a=moment(2)/moment(1)
p=moment(3)-moment(2)**2/moment(1)
c=-10*a*a*moment(2)+168*a*moment(3)-60*moment(4)
assert a==F(1,55) and p==F(81,1100000000) and c==F(-3347,12100000000)
assert F(5,12)*10**20*F(1,10**10)**4==F(1,240000000000000000000)
print('PASS: six candidate coefficients, 64 exact stencil pairs, rational counterexample, and extrapolation constant.')
print('This test does not prove the all-order stencil identity or canonical sign.')
