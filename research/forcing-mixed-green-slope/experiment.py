#!/usr/bin/env python3
"""Independent exact-rational matrix checks, not a native-source certificate."""
from fractions import Fraction as F
from pathlib import Path
import json

def C(r=0, s=0): return F(r), F(s)
def add(z, w): return z[0]+w[0], z[1]+w[1]
def neg(z): return -z[0], -z[1]
def sub(z, w): return add(z, neg(w))
def mul(z, w): return z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0]
def conj(z): return z[0], -z[1]
def normsq(z): return z[0]**2+z[1]**2
def div(z, w):
    assert normsq(w)
    p=mul(z, conj(w))
    return p[0]/normsq(w), p[1]/normsq(w)
def total(values):
    result=C()
    for value in values: result=add(result,value)
    return result
def form(matrix, c, e):
    return total(mul(mul(conj(c[i]),matrix[i][j]),e[j])
                 for i in range(len(c)) for j in range(len(e)))

# Synthetic finite carrier: exact complex Euclidean two-coordinate space.
def vadd(x,y): return tuple(add(a,b) for a,b in zip(x,y))
def vscale(z,x): return tuple(mul(z,a) for a in x)
def vsub(x,y): return vadd(x,vscale(C(-1),y))
def ip(x,y): return total(mul(conj(a),b) for a,b in zip(x,y))
def padd(x,y): return vadd(x[0],y[0]),vadd(x[1],y[1])
def reduce(t,x): return vsub(x[0],vscale(C(a*t),x[1])),vscale(C(a*t),x[0])
def green(x,y): return sub(ip(x[1],y[0]),ip(x[0],y[1]))
a=F(3,5)
w=(C(2,1),C(1,-1))
zero=(C(),C())
def forcing(t): return C(1+t/3,t*t/7)
def cp(t): return ((C(t*(1+t),t*t),C(2*t,t**3)),(C(-t*t,t),C(t,2*t*t)))
def fp(t): return vscale(forcing(t),w),zero
def eta(t): return ip(w,cp(t)[0])
def gamma(t): return ip(w,cp(t)[1])
def mixed(t,u): return add(green(reduce(t,cp(t)),reduce(u,fp(u))),green(reduce(t,fp(t)),reduce(u,cp(u))))
def first(t,u): return mul(C(-a),add(mul(conj(forcing(t)),eta(u)),mul(conj(eta(t)),forcing(u))))
def retained(t,u):
    if t==u: return C() # Total-division convention; NOT a confluent claim.
    return mul(C(a*a*t*u),div(sub(mul(conj(gamma(t)),forcing(u)),mul(conj(forcing(t)),gamma(u))),C(u-t)))
def chi(t): return div(neg(gamma(t)),forcing(t))
def center(c,t): return [div(neg(total(mul(ci,forcing(ti)) for ci,ti in zip(c,t))),forcing(F(0)))]+c
def hidden(x):
    def q(v): return tuple(div(z,C(2)) for z in (sub(v[0],v[1]),sub(v[1],v[0])))
    return q(x[0]),q(x[1])
def readout(x): return total(x[0]),total(x[1])
def scalar_green(x,y): return sub(mul(conj(x[1]),y[0]),mul(conj(x[0]),y[1]))
checks=[]
for N,M in [(1,1),(2,3),(4,2),(3,5)]:
    t=[F(i+1,10) for i in range(N)]
    u=[F(j+1,11) for j in range(M)]
    c=[C(F(i+1,i+2),F(1,i+3)) for i in range(N)]
    d=[C(F(j+2,j+3),F(-1,j+4)) for j in range(M)]
    tc,uc=[F(0)]+t,[F(0)]+u
    chat,dhat=center(c,t),center(d,u)
    for ti in t:
        for uj in u:
            assert ti!=uj
            actual=div(mixed(ti,uj),C(uj-ti))
            assert actual==add(first(ti,uj),retained(ti,uj))
            anchored=sub(sub(actual,mul(conj(div(forcing(ti),forcing(F(0)))),div(mixed(F(0),uj),C(uj)))),
                         mul(div(mixed(ti,F(0)),C(-ti)),div(forcing(uj),forcing(F(0)))))
            assert anchored==retained(ti,uj)
            ratio=mul(C(a*a*ti*uj),mul(mul(conj(forcing(ti)),forcing(uj)),div(sub(chi(uj),conj(chi(ti))),C(uj-ti))))
            assert ratio==retained(ti,uj)
            x,y=reduce(ti,padd(cp(ti),fp(ti))),reduce(uj,padd(cp(uj),fp(uj)))
            assert green(x,y)==add(mul(C(F(1,2)),scalar_green(readout(x),readout(y))),green(hidden(x),hidden(y)))
    assert form([[first(ti,uj) for uj in uc] for ti in tc],chat,dhat)==C()
    assert form([[retained(ti,uj) for uj in uc] for ti in tc],chat,dhat)==form([[retained(ti,uj) for uj in u] for ti in t],c,d)
    checks.append({'N':N,'M':M,'original_pair_crosses':True,'hidden_both_orientations':True})
controls=[]
for coef in [F(1,8),F(1),F(16)]:
    s=coef/(10*(1+coef))
    ell=lambda t,u:coef-(t*t+t*u+u*u)
    q=ell(0,0)-ell(0,s)-ell(s,0)+ell(s,s)
    assert q==-s*s<0 and ell(0,0)>0 and ell(s,s)>0
    # Same positive first jet, non-real higher phase: not the native chi.
    phase=lambda t:C(coef*t,t*t)
    assert sub(phase(s),conj(phase(s)))==C(0,2*s*s)!=C()
    controls.append({'C':str(coef),'s':str(s),'negative_form':str(q)})
result={'status':'PASS','arithmetic':'Fraction in both complex components',
        'provenance':'Synthetic controls; no canonical moment, zero, height or theta input.',
        'polarized_families':checks,'same_positive_jet_controls':controls,
        'diagonal_convention':'Isolated total division is not a physical confluent extension.'}
out=Path(__file__).resolve().parent/'evidence'
out.mkdir(exist_ok=True)
(out/'exact-controls.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 4 rectangular complex families; original Green quotient and hidden crossings; 3 indefinite positive-jet controls')
