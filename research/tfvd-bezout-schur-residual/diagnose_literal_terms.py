#!/usr/bin/env python3
"""Diagnostic only: literal completed C3 head, all four ordered terms.

No theta/zeta call and no heights/zeros input. Four reference coefficients
already enclosed by PR69 supply diagnostic centers, not new input intervals.
mpmath outputs are not Lean certificates.
"""
from pathlib import Path
import json
import mpmath as mp

mp.mp.dps = 70
c = [mp.mpf(s) for s in ('0.497120778188314', '-0.011485972157573',
                         '0.000123452018070', '-0.000000832355481')]
h = []
for n in range(3):
    h.append((-(n+1)*c[n+1]-sum(h[k]*c[n-k] for k in range(n)))/c[0])
z = [h[0]-h[1]/h[0], mp.mpf(1)]
target = c[0]**2*(h[2]-h[1]**2/h[0])

def multiplier(w):
    s = mp.mpf('0.5')+1j*w
    xi = s*(s-1)*mp.exp(-s*mp.log(mp.pi)/2)*mp.gamma(s/2)/2
    return xi/(1-mp.exp((1-s)*mp.log(3)))

a = mp.taylor(multiplier, 0, 6)
prefix = [mp.mpc(1)]+[mp.mpc(0)]*6

def head_coeffs():
    return [sum(a[k]*prefix[2*j-k] for k in range(2*j+1)) for j in range(4)]

def response(v,n):
    return -n*v[n] if n else 0

def term(v,w):
    return sum(z[i]*z[j]*sum(w[j-k]*response(v,i+k+1)-
                            response(v,j-k)*w[i+k+1] for k in range(j+1))
               for i in range(2) for j in range(2))

def budget(v,w):
    return sum(abs(z[i])*abs(z[j])*sum(abs(w[j-k])*abs(response(v,i+k+1))+
                     abs(response(v,j-k))*abs(w[i+k+1]) for k in range(j+1))
               for i in range(2) for j in range(2))

rows=[]
accelerated_rows=[]
for M in range(4097):
    if M in (0,1,4,16,64,256,1024,4096):
        head=head_coeffs()
        tail=[c[j]-head[j] for j in range(4)]
        terms=[term(head,head),term(head,tail),term(tail,head),term(tail,tail)]
        err=budget(head,tail)+budget(tail,head)+budget(tail,tail)
        assert abs(sum(terms)-target)<mp.mpf('1e-60')
        row=dict(M=M, HH=mp.nstr(terms[0].real,18),HT=mp.nstr(terms[1].real,18),
                 TH=mp.nstr(terms[2].real,18),TT=mp.nstr(terms[3].real,18),
                 sum=mp.nstr(sum(terms).real,18), budget=mp.nstr(err,18),
                 margin_test_at_reference_centers=bool(terms[0].real>err),
                 max_imaginary_even_head=mp.nstr(max(abs(v.imag) for v in head),5))
        rows.append(row)
        print(row,flush=True)
        if M==64:
            weights=[mp.mpf(k)/729 for k in
              (728,-1444,638,1092,-2445,2640,-1911,987,-363,91,-14,1)]
            boundary=[sum(weights[k]*mp.exp(-mp.log(3*M+2+k)/2)*
              (-1j*mp.log(3*M+2+k))**r/mp.factorial(r) for k in range(12)) for r in range(7)]
            completed_boundary=[sum(a[k]*boundary[2*j-k] for k in range(2*j+1)) for j in range(4)]
            ah=[head[j]+completed_boundary[j] for j in range(4)]
            at=[tail[j]-completed_boundary[j] for j in range(4)]
            ats=[term(ah,ah),term(ah,at),term(at,ah),term(at,at)]
            ae=budget(ah,at)+budget(at,ah)+budget(at,at)
            assert abs(sum(ats)-target)<mp.mpf('1e-60')
            ar=dict(M=M,exact_C3_boundary_repartition=True,
               HH=mp.nstr(ats[0].real,18),HT=mp.nstr(ats[1].real,18),
               TH=mp.nstr(ats[2].real,18),TT=mp.nstr(ats[3].real,18),
               sum=mp.nstr(sum(ats).real,18),budget=mp.nstr(ae,18),
               margin_test_at_reference_centers=bool(ats[0].real>ae),
               maximum_tail_coefficient=mp.nstr(max(abs(v) for v in at),18))
            accelerated_rows.append(ar)
            print('EXACT BOUNDARY REPARTITION:',ar,flush=True)
    if M==4096: break
    for addr,weight in ((3*M+2,1),(3*M+3,-2),(3*M+4,1)):
        log=mp.log(addr)
        amp=mp.exp(-log/2)
        for r in range(7):
            prefix[r]+=weight*amp*(-1j*log)**r/mp.factorial(r)

root=Path(__file__).resolve().parent
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/literal-terms-diagnostic.json').write_text(json.dumps(dict(
    status='NUMERICAL_DIAGNOSTIC_NOT_CERTIFICATE', dps=70,
    original_gamma_xi_chart=True, original_c3_addresses=True,
    reference_coefficients_from_PR69=True, rows=rows, accelerated_rows=accelerated_rows),indent=2)+'\n')
