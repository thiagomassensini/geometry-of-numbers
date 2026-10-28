#!/usr/bin/env python3
"""Exact polarized/stencil regressions; canonical Decimal data are diagnostic only."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D, localcontext
import csv,hashlib,json
root=Path(__file__).resolve().parent
evidence=root/'evidence';evidence.mkdir(exist_ok=True)
checkpoint=Path('/home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv')
expected='05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833'
assert hashlib.sha256(checkpoint.read_bytes()).hexdigest()==expected

def add(a,b):return (a[0]+b[0],a[1]+b[1])
def neg(a):return (-a[0],-a[1])
def sub(a,b):return add(a,neg(b))
def conj(a):return (a[0],-a[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
I=(F(0),F(1));two=(F(2),F(0))
values=[(F(i,3),F(j,5)) for i in range(-2,3) for j in range(-2,3)]
polarized=0
for q in values:
    for r in values:
        lhs=sub(mul(conj(add(q,I)),add(r,I)),mul(conj(sub(q,I)),sub(r,I)))
        rhs=mul(mul(two,I),sub(conj(q),r))
        assert lhs==rhs
        polarized+=1

def padd(a,b):
    r=dict(a)
    for k,v in b.items():r[k]=r.get(k,F(0))+v
    return {k:v for k,v in r.items() if v}
def pmul(a,b):
    r={}
    for k,x in a.items():
        for l,y in b.items():r[k+l]=r.get(k+l,F(0))+x*y
    return {k:v for k,v in r.items() if v}
stencil=0
for a in [F(0),F(-1),F(7,1000),F(2,5)]:
    w=[{0:F(-1),2:-6*a},{0:F(3),2:6*a},{0:F(-3)},{0:F(1)}]
    targets=[{}, {0:a*a}, {0:-2*a,2:-5*a*a},
             {0:F(1),2:84*a,4:21*a*a}, {2:F(-30),4:-1974*a,6:-85*a*a}]
    for n in range(5):
        m=2*n+1;p={}
        for i in range(4):
            for j in range(4):
                c=F((-1)**n*((i+1)**m+(j+1)**m),36*(i+j+2))
                p=padd(p,pmul(pmul(w[i],w[j]),{m-7:c}))
                stencil+=1
        target={k:v for k,v in targets[n].items() if v}
        assert p==target,(a,n,p,target)

with localcontext() as ctx:
    ctx.prec=120
    moments=[D(row['canonical_h']) for row in csv.DictReader(checkpoint.open())]
    h1,h2,h3,h4=moments[1:5]
    a=h2/h1;limit=2*(h3-2*a*h2+a*a*h1)
    correction=-10*a*a*h2+168*a*h3-60*h4
    polynomial=-10*h2**3+168*h1*h2*h3-60*h1*h1*h4
    assert correction>0 and polynomial>0
    assert abs(correction*h1*h1-polynomial)<D('1e-120')
    samples=[]
    for den in [10,20,50,100]:
        t=1/D(den);w=[-1-6*a*t*t,3+6*a*t*t,D(-3),D(1)]
        g=[]
        for degree in range(1,5):
            s=t*degree
            g.append(sum(2*D((-1)**n)*hn*s**(2*n+1) for n,hn in enumerate(moments)))
        incident=sum(w[i]*w[j]*(g[i]+1)*(g[j]+1)/D(i+j+2)
                     for i in range(4) for j in range(4))/(72*t**7)
        returned=sum(w[i]*w[j]*(g[i]-1)*(g[j]-1)/D(i+j+2)
                     for i in range(4) for j in range(4))/(72*t**7)
        energy=incident-returned
        readout=sum(w[i]*w[j]*(g[i]+g[j])/D(i+j+2)
                    for i in range(4) for j in range(4))/(36*t**7)
        assert abs(energy-readout)<D('1e-100')
        assert energy>limit
        samples.append({'h':str(t),'incident_energy':str(incident),'returned_energy':str(returned),
                        'full_balance':str(energy),'normalized_correction':str((energy-limit)/t**2)})
    record={'PASS':True,'exact_gaussian_polarized_checks':polarized,'exact_stencil_contributions':stencil,
        'input_column':'canonical_h','input_moments':len(moments),'checkpoint':str(checkpoint),
        'checkpoint_sha256':expected,'decimal_precision':120,'critical_parameter_diagnostic':str(a),
        'limit_diagnostic':str(limit),'correction_diagnostic':str(correction),
        'orientation_polynomial_diagnostic':str(polynomial),'samples':samples,
        'scope':'Decimal tests use an existing canonical-data prefix without a tail bound. Lean uses exact original source and the full analytic remainder. No new moments, zeros or heights were computed.'}
    (evidence/'mechanism-probe.json').write_text(json.dumps(record,indent=2)+'\n')
print(f'PASS: {polarized} exact polarized identities, {stencil} exact stencil contributions, 4 complete-channel diagnostics.')
