#!/usr/bin/env python3
"""Exact synthetic algebra controls; no native positivity or tail bound."""
from fractions import Fraction as F
import json

def z(a=0,b=0): return F(a),F(b)
def add(a,b): return a[0]+b[0],a[1]+b[1]
def neg(a): return -a[0],-a[1]
def sub(a,b): return add(a,neg(b))
def mul(a,b): return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def conj(a): return a[0],-a[1]
def total(xs):
    s=z()
    for x in xs:s=add(s,x)
    return s

def diff(f,n):return sub(f(n+1),f(n))
def bracket(f,n):return add(sub(f(n+2),mul(z(2),f(n+1))),f(n))
def flux(f,g,n):return sub(mul(conj(f(n)),diff(g,n)),mul(conj(f(0)),diff(g,0)))
def bulk(f,g,n):return total(mul(conj(f(k+1)),bracket(g,k)) for k in range(n))
functions=[lambda n:z(n*n+1,F(n,3)),lambda n:z(2-n,n*n*n-1),lambda n:z(F(1,n+1),F(n*n,7))]
parts=0
for f in functions:
 for g in functions:
  for n in [0,1,2,5,11]:
   lhs=total(mul(conj(diff(f,k)),diff(g,k)) for k in range(n))
   assert lhs==sub(flux(f,g,n),bulk(f,g,n))
   parts+=1

def green(x,y):return sub(mul(conj(x[1]),y[0]),mul(conj(x[0]),y[1]))
a,t,u=F(1,7),F(-2,3),F(3,5)
def reduced(x,y):
 return sub(mul(z(a*a*t*u),green(x,y)),mul(z(a*(u-t)/2),mul(conj(x[0]),y[0])))
def pair_add(x,y):return add(x[0],y[0]),add(x[1],y[1])
h=(z(2,3),z(F(4,3),-1)); ht=(z(F(-2,5),1),z(3,F(1,2)))
k=(z(-1,2),z(3,-4)); kt=(z(F(3,8),-2),z(F(-1,6),F(1,4)))
whole=reduced(pair_add(h,ht),pair_add(k,kt))
terms=[reduced(h,k),reduced(h,kt),reduced(ht,k),reduced(ht,kt)]
assert whole==total(terms)
assert sub(whole,terms[0])==total(terms[1:])
assert all(x!=z() for x in terms[1:])
print(json.dumps({'status':'PASS','scope':'synthetic exact algebra',
 'polarized_parts_checks':parts,'reduced_tail_crosses_nonzero':3,
 'native_moment_sign_proved':False},indent=2))
