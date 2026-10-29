#!/usr/bin/env python3
"""Exact stencil regression plus an explicitly NON-proof canonical-data probe."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
import csv, hashlib, json

root=Path(__file__).resolve().parent
evidence=root/'evidence'; evidence.mkdir(exist_ok=True)
checkpoint=Path('/home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv')
expected='05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833'
assert hashlib.sha256(checkpoint.read_bytes()).hexdigest()==expected

def add(a,b):
    r=dict(a)
    for k,v in b.items(): r[k]=r.get(k,F(0))+v
    return {k:v for k,v in r.items() if v}
def mul(a,b):
    r={}
    for i,x in a.items():
        for j,y in b.items(): r[i+j]=r.get(i+j,F(0))+x*y
    return {k:v for k,v in r.items() if v}
def scale(a,x): return {k:v*x for k,v in a.items() if v*x}

w=[{0:F(-1),2:F(-21,500)}, {0:F(3),2:F(21,500)}, {0:F(-3)}, {0:F(1)}]
expected_polys=[{}, {7:F(441,250000)}, {7:F(-63,125),9:F(-441,50000)},
                {7:F(36),9:F(2646,125),11:F(9261,250000)}]
checks=0
for n in range(4):
    m=2*n+1
    p={}
    for i in range(4):
        for j in range(4):
            f=F((-1)**n*((i+1)**m+(j+1)**m),i+j+2)
            p=add(p,mul(mul(w[i],w[j]),{m:f}))
            checks+=1
    assert p==expected_polys[n], (n,p)

with localcontext() as ctx:
    ctx.prec=120
    rows=list(csv.DictReader(checkpoint.open()))
    h=[D(row['canonical_h']) for row in rows]
    a,b,c,d=[2*x for x in h[:4]]
    mu=[a,3*b-a**3,5*c-5*a*a*b+a**5,
        7*d-7*a*a*c-7*a*b*b+7*a**4*b-a**7]
    witness=F(7,1000)
    u=D(witness.numerator)/D(witness.denominator)
    W=u*u*mu[1]-2*u*mu[2]+mu[3]
    assert W<0
    samples=[]
    for denom in [10,20,50,100]:
        t=1/D(denom)
        ww=[-1-6*u*t*t,3+6*u*t*t,D(-3),D(1)]
        ss=[]; qq=[]
        for degree in range(1,5):
            s=t*degree
            g=sum(2*D((-1)**n)*hn*s**(2*n+1) for n,hn in enumerate(h))
            gp=sum(2*D((-1)**n)*hn*(2*n+1)*s**(2*n) for n,hn in enumerate(h))
            ss.append(s*gp/(1-g*g))
            qq.append((g-1)/(g+1))
        psi=sum(ww[i]*ww[j]*(ss[i]+ss[j])/D(i+j+2)
                for i in range(4) for j in range(4))
        assert psi<0
        # Congruence for the scalar quotient, as an independent algebra check.
        vv=[ww[i]/qq[i] for i in range(4)]
        derivative=sum(vv[i]*vv[j]*(2/t)*qq[i]*qq[j]*(ss[i]+ss[j])/D(i+j+2)
                       for i in range(4) for j in range(4))
        assert abs(derivative-2*psi/t)<D('1e-110')
        samples.append({'h':str(t),'full_16_crosses':str(psi),
                        'normalized_by_h7':str(psi/t**7),
                        'scalar_derivative_congruence':str(derivative)})
    result={'PASS':True,'exact_stencil_terms_checked':checks,
        'checkpoint':str(checkpoint),'checkpoint_sha256':expected,
        'input_column':'canonical_h','input_moments':len(h),'decimal_precision':120,
        'flow_coefficients_diagnostic':[str(x) for x in mu],
        'rational_witness':'(7/1000,1)','W_diagnostic':str(W),'limit_36W_diagnostic':str(36*W),
        'samples':samples,
        'scope':'Decimal probes use a fixed canonical-data Taylor prefix without an analytic tail bound; NOT a positivity certificate. Lean uses original analytic response, exact integral boxes and full analytic remainder instead.'}
    (evidence/'mechanism-probe.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 64 exact stencil contributions and 4 full-cross scalar diagnostic probes; no new moments calculated.')
