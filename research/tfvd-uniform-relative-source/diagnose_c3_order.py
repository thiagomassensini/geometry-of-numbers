#!/usr/bin/env python3
"""Diagnostic only, not interval-certified: original C3/64 head and four terms."""
import csv
import sys
from mpmath import mp

mp.dps = 70
path = sys.argv[1] if len(sys.argv) > 1 else "/home/thlinux/momentos/investigations/jacobi_polynomial_moments_20261024/c2_momentos_16_excerpt.csv"
with open(path, newline="") as f:
    h = [mp.mpf(row["h_k"]) for row in csv.DictReader(f)]
s = mp.mpf("0.5")
c = [s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)/2]
r = 3
for n in range(2*r):
    c.append(-mp.fsum(h[k] * c[n-k] for k in range(n+1))/(n+1))

def multiplier(w):
    s = mp.mpf("0.5")+1j*w
    xi = s*(s-1)*mp.exp(-s*mp.log(mp.pi)/2)*mp.gamma(s/2)/2
    return xi/(1-mp.exp((1-s)*mp.log(3)))

highest=2*(2*r)
a=mp.taylor(multiplier,0,highest)
prefix=[mp.mpc(1)]+[mp.mpc(0)]*highest
for M in range(64):
    for addr,weight in ((3*M+2,1),(3*M+3,-2),(3*M+4,1)):
        log=mp.log(addr); amp=mp.exp(-log/2)
        for q in range(highest+1):
            prefix[q]+=weight*amp*(-1j*log)**q/mp.factorial(q)
head=[mp.fsum(a[k]*prefix[2*j-k] for k in range(2*j+1)) for j in range(2*r+1)]
weights=[mp.mpf(k)/729 for k in (728,-1444,638,1092,-2445,2640,-1911,987,-363,91,-14,1)]
boundary=[mp.fsum(weights[k]*mp.exp(-mp.log(194+k)/2)*(-1j*mp.log(194+k))**q/mp.factorial(q) for k in range(12)) for q in range(highest+1)]
acc=[head[j]+mp.fsum(a[k]*boundary[2*j-k] for k in range(2*j+1)) for j in range(2*r+1)]
tail=[c[j]-acc[j] for j in range(2*r+1)]

print("tail_coeff_abs",[mp.nstr(abs(x),8) for x in tail])

def response(v,sector,k):
    return -(k+1)*v[k+1] if sector else (-k*v[k] if k else 0)

def term(v,w,sector,z):
    return mp.fsum(z[i]*z[j]*mp.fsum(w[j-k]*response(v,sector,i+k+1)-response(v,sector,j-k)*w[i+k+1] for k in range(j+1)) for i in range(r) for j in range(r))

def budget(v,w,sector,z):
    return mp.fsum(abs(z[i])*abs(z[j])*mp.fsum(abs(w[j-k])*abs(response(v,sector,i+k+1))+abs(response(v,sector,j-k))*abs(w[i+k+1]) for k in range(j+1)) for i in range(r) for j in range(r))

for sector in (0,1):
    n=r-1
    A=mp.matrix([[h[i+j+sector] for j in range(n)] for i in range(n)])
    b=mp.matrix([h[i+n+sector] for i in range(n)])
    x=mp.lu_solve(A,-b)
    pivot=h[2*n+sector]+mp.fdot(b,x)
    v=mp.matrix(list(x)+[mp.mpf(1)])
    T=mp.matrix([[c[i-j] if i>=j else 0 for j in range(r)] for i in range(r)])
    z=mp.lu_solve(T.T,c[0]*v)
    terms=[term(acc,acc,sector,z),term(acc,tail,sector,z),term(tail,acc,sector,z),term(tail,tail,sector,z)]
    E=budget(acc,tail,sector,z)+budget(tail,acc,sector,z)+budget(tail,tail,sector,z)
    mass=mp.fsum(abs(t) for t in z)
    ones=[mp.mpf(1)]*r
    Eone=budget(acc,tail,sector,ones)+budget(tail,acc,sector,ones)+budget(tail,tail,sector,ones)
    aval=mp.fsum(abs(t) for t in c)
    rho=mp.mpf(96)*mp.factorial(14)/(729*mp.mpf(191)**13)*mp.mpf(4)**(4*r)
    coarse=4*r*r*(2*aval*rho+3*rho**2)*mass**2
    target=c[0]**2*pivot
    print("sector",sector,"HH",mp.nstr(terms[0].real,16),"full",mp.nstr(target,16),"budget",mp.nstr(E,12),"coarse",mp.nstr(coarse,12),"coarse_over_target",mp.nstr(coarse/target,12),"E_one_times_mass2",mp.nstr(Eone*mass**2,12),"HH_gt_budget",terms[0].real>E,"HH_gt_uniform",terms[0].real>Eone*mass**2,"HH_gt_coarse",terms[0].real>coarse)
    print("crosscheck_abs",mp.nstr(abs(mp.fsum(terms)-target),5),"mass",mp.nstr(mass,12))
print("status numerical_diagnostic_not_interval_certified")
