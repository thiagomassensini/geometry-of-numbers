#!/usr/bin/env python3
"""Exact telescoping controls and diagnostics of the original six-source readout."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
from functools import lru_cache
import csv, hashlib, json

root=Path(__file__).resolve().parent
evidence=root/'evidence';evidence.mkdir(exist_ok=True)
checkpoint=Path('/home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv')
expected='05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833'
assert hashlib.sha256(checkpoint.read_bytes()).hexdigest()==expected

checks=0
for K in range(8):
    for M in range(16):
        # Two independent rational components, i.e. exact complex readouts.
        for c in range(2):
            def f(k): return F((-1)**(k+c),k+1+c)+F(k*k+3*c,11+k)
            assert sum((f(K+j)-f(K+j+1) for j in range(M)),F(0))==f(K)-f(K+M)
            checks+=1
zero_controls=0
for K in range(1,30):
    f=lambda k:F(1,(k+1)**2)
    assert 0<f(K+1)<f(K)
    for c in [F(-2),F(0),F(7,9)]:
        assert (f(K)+c)-(f(K+1)+c)==f(K)-f(K+1)
        zero_controls+=1

with localcontext() as ctx:
    ctx.prec=160
    h=[D(r['canonical_h']) for r in csv.DictReader(checkpoint.open())]
    delta=h[1]*h[3]-h[2]**2
    u=(h[2]*h[3]-h[1]*h[4])/delta;v=(h[2]*h[4]-h[3]**2)/delta
    L=2*(h[5]+2*u*h[4]+(u*u+2*v)*h[3]+2*u*v*h[2]+v*v*h[1])
    C=-10*v*v*h[2]-168*u*v*h[3]-60*(u*u+14*v)*h[4]-484*u*h[5]-182*h[6]
    d1=[-1,1,0,0,0,0];d3=[-1,3,-3,1,0,0];d5=[-1,5,-10,10,-5,1]
    @lru_cache(None)
    def balance(den):
        t=1/D(den)
        w=[D(d5[i])-20*u*t*t*D(d3[i])+120*v*t**4*D(d1[i]) for i in range(6)]
        g=[sum(2*D((-1)**n)*hn*((i+1)*t)**(2*n+1) for n,hn in enumerate(h)) for i in range(6)]
        return sum(w[i]*w[j]*(g[i]+g[j])/D(i+j+2) for i in range(6) for j in range(6))/(14400*t**11)
    samples=[];decrements=0
    for den in [20,50,100,200]:
        partial=D(0)
        for j in range(den):
            drop=balance(den+j)-balance(den+j+1)
            assert drop>0
            partial+=drop;decrements+=1
        assert abs(partial-(balance(den)-balance(2*den)))<D('1e-145')
        remaining=balance(2*den)-L
        assert remaining>0 and abs(balance(den)-partial-remaining-L)<D('1e-145')
        samples.append({'denominator':den,'anchor_balance':str(balance(den)),
          'ordered_partial_tail':str(partial),'remaining_tail_diagnostic':str(remaining),
          'full_tail_diagnostic':str(balance(den)-L),
          'tail_over_h_squared':str((balance(den)-L)*den**2)})
    record={'PASS':True,'exact_complex_telescoping_checks':checks,
      'exact_constant_shift_controls':zero_controls,'positive_decimal_decrements':decrements,
      'checkpoint':str(checkpoint),'checkpoint_sha256':expected,'input_column':'canonical_h',
      'input_moments':len(h),'decimal_precision':160,'limit_diagnostic':str(L),
      'correction_diagnostic':str(C),'samples':samples,
      'scope':'Exact Fraction controls are algebra, not alternate physical sources. Decimal readouts retain all 36 source crosses but use a finite existing moment prefix without a tail bound. Lean proves monotonicity and summability using the complete analytic remainder; diagnostics do not provide its threshold or an all-order sign.'}
    (evidence/'mechanism-probe.json').write_text(json.dumps(record,indent=2)+'\n')
print(f'PASS: {checks} exact complex telescopes, {zero_controls} exact constant-shift controls, {decrements} diagnostic native decrements, 4 complete-tail diagnostics.')
