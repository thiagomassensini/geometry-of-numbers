#!/usr/bin/env python3
"""Independent exact rational probe: original coefficient/Cauchy route vs grid route.
Diagnostic samples only: no canonical moments, zeros, heights or source replacement.
"""
from fractions import Fraction as F
from pathlib import Path
import json
root=Path(__file__).resolve().parent

def divided(x,y):
    if len(x)==1: return y[0]
    return (divided(x[1:],y[1:])-divided(x[:-1],y[:-1]))/(x[-1]-x[0])

def beta(kappa,a):
    A=kappa**3;B=a*kappa
    return [-A/6-B,A/2+B,-A/2,A/6]

def kernel(q,p,w):
    return sum(q[i]*p[j]*w[j]/F(i+j+2) for i in range(4) for j in range(4))

records=[]
for n in [2,3,32]:
    kap=F(n);e=1/kap**2;x=[e*t for t in [1,4,9,16]]
    f=[1/(1+t)**2 for t in x]
    w=[F(j+1)/kap*f[j] for j in range(4)]
    d1=divided(x[:2],f[:2]);d2=divided(x[:3],f[:3]);d3=divided(x,f)
    for a,b in [(F(0),F(0)),(F(1),F(2)),(F(3,2),F(3,2)),(F(-1),F(2))]:
        original=kap*(kernel(beta(kap,a),beta(kap,b),w)+kernel(beta(kap,b),beta(kap,a),w))
        pol=[1+(a+b)*(t+12*e)+a*b*(t-9*e)*(t-16*e) for t in x]
        grid=-divided(x,[p*y for p,y in zip(pol,f)])
        curvature=-d3-(a+b)*(d2+28*e*d3)-a*b*d1
        shifted=[(1+a*(t+12*e))*(1+b*(t+12*e))*y for t,y in zip(x,f)]
        defect=-divided(x,shifted)+49*a*b*e*divided(x,[t*y for t,y in zip(x,f)])
        assert original==grid==curvature==defect
        records.append({'kappa':n,'a':str(a),'b':str(b),'all_four_routes_equal':True,'balance':str(original)})
    if n==32:
        c=-d3-3*(d2+28*e*d3)-F(9,4)*d1
        assert d1<0<d2 and d3<0 and d2+28*e*d3>0 and c<0
        witness={'kappa':n,'epsilon':str(e),'first':str(d1),'second':str(d2),
                 'third':str(d3),'mixed_entry':str(d2+28*e*d3),'critical_negative':str(c),
                 'is_native_response':False}
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/mechanism-probe.json').write_text(json.dumps({'checks':records,'witness':witness,
    'purpose':'diagnostic of scalar sign sufficiency, not a canonical-source counterexample'},indent=2)+'\n')
print('PASS: 12 exact rational comparisons of four independent expressions; diagnostic negative witness.')
