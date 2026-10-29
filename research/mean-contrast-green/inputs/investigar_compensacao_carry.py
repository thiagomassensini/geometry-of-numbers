#!/usr/bin/env python3
"""Investigação reproduzível: Gram ímpar / divisibilidade / Green jet zero.
Sources (out-of-band): native-carry-spectral-weyl PR15, geometry-of-numbers PR41/82,
primos PR47. No canonical Hankel positivity inferred from camera Gram.
"""
import json
import math
from pathlib import Path
import mpmath as mp
import sympy as sp

OUT = Path('/mnt/data')
BASES = list(range(3, 22, 2))

def periodic(b, c):
    return sp.Integer(math.gcd(b, c) - 1)

def level(b, c):
    return sp.Integer(min(b, c) * (math.gcd(b, c) - 1))

def schur_data(kernel):
    rows = []
    for i, b in enumerate(BASES):
        prior = BASES[:i]
        diag = kernel(b, b)
        if prior:
            A = sp.Matrix([[kernel(x, y) for y in prior] for x in prior])
            v = sp.Matrix([kernel(x, b) for x in prior])
            inherited = (v.T * A.inv() * v)[0]
        else:
            inherited = sp.Integer(0)
        new = sp.factor(diag - inherited)
        phi = sp.totient(b)
        rows.append({
            'base': b,
            'total': str(diag),
            'inherited': str(inherited),
            'new_schur': str(new),
            'phi': int(phi),
            'inherited_percent': float(inherited / diag * 100),
            'new_divisor_lower_bound': str(b * phi),
        })
        assert new > 0
        if kernel is periodic:
            assert new == phi
        else:
            assert new >= b * phi
    return rows

def check_camera_exact():
    for b in BASES:
        for c in BASES:
            L = math.lcm(b, c)
            brute = sp.Rational(sum((1-b*(i % b == 0))*(1-c*(i % c == 0)) for i in range(L)), L)
            assert brute == periodic(b,c), (b,c, brute,periodic(b,c))
            totient_factor = sum(sp.totient(d) for d in range(2,math.gcd(b,c)+1) if b%d==0 and c%d==0)
            assert totient_factor == periodic(b,c)
    for b in BASES:
        coprime_residue_count = sum(math.gcd(r,b)==1 for r in range(1,b))
        assert coprime_residue_count == sp.totient(b)

    M = sp.Matrix([[periodic(b,c) for c in BASES] for b in BASES])
    L = sp.Matrix([[sp.sqrt(sp.totient(c)) if b%c==0 else 0 for c in BASES] for b in BASES])
    assert (L*L.T-M).is_zero_matrix
    assert M.det() == sp.prod(sp.totient(b) for b in BASES)
    N = sp.Matrix([[level(b,c) for c in BASES] for b in BASES])
    assert all(v > 0 for v in (M[:k,:k].det() for k in range(1,len(BASES)+1)))
    assert all(v > 0 for v in (N[:k,:k].det() for k in range(1,len(BASES)+1)))
    return {'bases':BASES,'periodic_determinant':str(M.det()),'level_determinant':str(N.det()),
            'periodic':schur_data(periodic), 'level':schur_data(level)}


def characteristic(z):
    s=mp.mpf('0.5')+1j*z
    return (s*(s-1)/2)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)

def response(z):
    return -mp.diff(characteristic,z)/(2*characteristic(z))

def jclosed(eta):
    return (1/(1-eta)+mp.log(1-eta)-1)/eta**2-mp.mpf('0.5')

def jquad(eta):
    return mp.quad(lambda t:t**2*eta*(2-eta*t)/(1-eta*t)**2,[0,1])

def check_green():
    mp.mp.dps=55
    h0=mp.re(-mp.diff(characteristic,0,2)/(2*characteristic(0)))
    etas=[mp.mpf('0.25'),mp.mpf('0.4'),mp.mpf('0.5'),1/mp.sqrt(2),mp.mpf('0.8')]
    threshold=mp.findroot(lambda e:jclosed(e)-mp.mpf('0.5'),(mp.mpf('0.35'),mp.mpf('0.5')))
    rows=[]
    for eta in etas:
        J=jclosed(eta)
        assert abs(J-jquad(eta))<mp.mpf('1e-48')
        rows.append({'eta':mp.nstr(eta,18),'J':mp.nstr(J,20),
            'bulk_over_h0_limit':mp.nstr(1-2*J,19),
            'mixed_over_h0_limit':mp.nstr(2*J,19),
            'sum':mp.nstr((1-2*J)+(2*J),19)})
    finite=[]
    eta=1/mp.sqrt(2)
    J=jclosed(eta)
    for kappa in (10,100,1000):
        z0=mp.j/mp.mpf(kappa)
        z1=2*z0
        r0=response(z0);r1=response(z1)
        assert abs(mp.re(r0)) < mp.mpf('1e-50')
        assert abs(mp.re(r1)) < mp.mpf('1e-50')
        a=mp.im(r0); delta=mp.im(r1-r0)
        total=mp.mpf(kappa)*a
        bulk=total-2*kappa*delta*J
        mixed=2*kappa*delta*J
        assert abs(bulk+mixed-total)<mp.mpf('1e-48')
        finite.append({'kappa':kappa,'total':mp.nstr(total,18),
           'bulk':mp.nstr(bulk,18),'mixed':mp.nstr(mixed,18),
           'bulk_over_total':mp.nstr(bulk/total,16),
           'mixed_over_total':mp.nstr(mixed/total,16),
           'error_from_h0':mp.nstr(total-h0,14)})
    # Independently integrate original chiral BB/BR sector definitions at kappa=10.
    kappa=10
    z0=mp.j/kappa; z1=2*z0
    r0=response(z0);r1=response(z1)
    ap=mp.sqrt(2)*r0+mp.j/mp.sqrt(2)
    am=mp.sqrt(2)*r0-mp.j/mp.sqrt(2)
    delta=mp.sqrt(2)*(r1-r0)
    def residual(t):return mp.sqrt(kappa)*delta*eta*(2-eta*t)/(1-eta*t)**2*t**mp.mpf('1.5')
    def BP(t):return mp.sqrt(kappa*t)*ap-residual(t)
    def BM(t):return mp.sqrt(kappa*t)*am-residual(t)
    BB=mp.quad(lambda t:(abs(BP(t))**2-abs(BM(t))**2)/2,[0,1])
    BR=mp.quad(lambda t:(mp.conj(BP(t))*residual(t)-mp.conj(BM(t))*residual(t))/2,[0,1])
    a=mp.im(r0);dr=mp.im(r1-r0)
    target_total=mp.mpf(kappa)*a
    target_bulk=target_total-2*kappa*dr*J
    target_mixed=2*kappa*dr*J
    assert abs(BB-target_bulk)<mp.mpf('1e-47')
    assert abs(2*mp.re(BR)-target_mixed)<mp.mpf('1e-47')
    assert abs(BB+2*mp.re(BR)-target_total)<mp.mpf('1e-47')
    return {'h0':mp.nstr(h0,34),'critical_eta':mp.nstr(eta,25),
      'J_threshold':mp.nstr(threshold,25),'eta_sweep':rows,'kappa_sweep':finite,
      'direct_integral_error':mp.nstr(abs(BB+2*mp.re(BR)-target_total),10)}

def check_logclock():
    mp.mp.dps=55
    a=2*mp.log(3);b=mp.log(5)
    rows=[]
    for k in (2,4,6):
        full=(a+b)**k
        nonmixed=a**k+b**k
        rows.append({'order':k,'mixed_fraction':mp.nstr(1-nonmixed/full,18)})
    assert abs(a+b-mp.log(45))<mp.mpf('1e-50')
    return rows

if __name__ == '__main__':
    result={'method':'Exact finite rationals for odd-camera Gram; high-precision diagnostic for jet-zero Green',
            'camera':check_camera_exact(),'green':check_green(),'logclock':check_logclock(),
            'limits':['Periodic camera Gram != moment Hankel','Varying eta is parameter stress-test, not physical multibase certificate',
                      'Green scalar diagnostic reuses completed xi identity, not raw material re-synthesis',
                      'BB+mixed conservation in finite probe follows algebraically from B=X-E and equal residual legs']}
    target=OUT/'experimento_compensacao_carry_20261024.json'
    target.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
    print('PASS: 100 direct period means, exact Gram determinant/pivots, Gram factorization, Green high precision and direct profile integrals')
    print('Exact determinant periodic:',result['camera']['periodic_determinant'])
    for p,l in zip(result['camera']['periodic'],result['camera']['level']):
        if p['base'] in [3,5,7,9,15,21]:
            print('base',p['base'],'periodic: inherited',p['inherited'],'residual',p['new_schur'],
                  'level: inherited',l['inherited'],'residual',l['new_schur'])
    print('eta where bulk changes sign:',result['green']['J_threshold'])
    print('physical eta rows:',result['green']['kappa_sweep'])
    print('log-clock mixed fractions:',result['logclock'])
    print('JSON:',target)
