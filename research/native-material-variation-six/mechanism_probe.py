#!/usr/bin/env python3
"""Independent exact Laurent derivative/complete-channel tests and data diagnostics."""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal as D,localcontext
import csv,hashlib,json,math
root=Path(__file__).resolve().parent
evidence=root/'evidence';evidence.mkdir(exist_ok=True)
checkpoint=Path('/home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_A/moments.csv')
expected='05734f8898aae995d77360c79e60521855181fede3f7f2a46c6b1bc1bc8e1833'
assert hashlib.sha256(checkpoint.read_bytes()).hexdigest()==expected
Z=(F(0),F(0))
def G(a=0,b=0):return (F(a),F(b))
def ga(a,b):return (a[0]+b[0],a[1]+b[1])
def gn(a):return (-a[0],-a[1])
def gs(a,b):return ga(a,gn(b))
def gc(a):return (a[0],-a[1])
def gm(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def gscale(a,t):return (a[0]*t,a[1]*t)
def pa(a,b):
    out=dict(a)
    for k,v in b.items():out[k]=ga(out.get(k,Z),v)
    return {k:v for k,v in out.items() if v!=Z}
def ps(a,b):return pa(a,{k:gn(v) for k,v in b.items()})
def pm(a,b):
    out={}
    for k,x in a.items():
        for j,y in b.items():out[k+j]=ga(out.get(k+j,Z),gm(x,y))
    return {k:v for k,v in out.items() if v!=Z}
def pscale(a,t):return {k:gscale(v,t) for k,v in a.items() if gscale(v,t)!=Z}
def pc(a):return {k:gc(v) for k,v in a.items()}
def pd(a):return {k-1:gscale(v,F(k)) for k,v in a.items() if k}
def pe(a,t):
    out=Z
    for k,v in a.items():out=ga(out,gscale(v,t**k))
    return out
def pair(r,x,y):
    out=Z
    for i in range(len(x)):
        for j in range(len(x)):
            out=ga(out,gscale(gm(gm(gc(x[i]),y[j]),ga(r[i],r[j])),F(1,i+j+2)))
    return out

whole_checks=0;derivative_checks=0
for N in range(1,7):
    for seed in [1,2,3]:
        rho=[{1:G(F(i+1,seed+2)),3:G(F(-(i+1)**3,19)),5:G(F((i+1)**5,701))} for i in range(N)]
        x=[{0:G(F(i-seed,5),F(seed+i,7)),1:G(F(2*i+1,11),F(-seed,13))} for i in range(N)]
        y=[{0:G(F(seed-i,17),F(2*seed+i,19)),2:G(F(i+1,23),F(seed-i,29))} for i in range(N)]
        E={};full={}
        for i in range(N):
            for j in range(N):
                xy=pm(pc(x[i]),y[j]);r=pa(rho[i],rho[j]);factor=F(1,i+j+2)
                E=pa(E,pm({-1:G(2*factor)},pm(xy,r)))
                gi=pscale(rho[i],F(2));gj=pscale(rho[j],F(2))
                defect=ps(pm(pa(gi,{0:G(1)}),pa(gj,{0:G(1)})),
                          pm(ps(gi,{0:G(1)}),ps(gj,{0:G(1)})))
                full=pa(full,pm({-1:G(factor/2)},pm(xy,defect)))
        assert E==full
        whole_checks+=1
        for t in [F(1,5),F(1,11),F(2,13)]:
            r=[pe(p,t) for p in rho];dr=[pe(pd(p),t) for p in rho]
            xx=[pe(p,t) for p in x];dx=[pe(pd(p),t) for p in x]
            yy=[pe(p,t) for p in y];dy=[pe(pd(p),t) for p in y]
            velocity=ga(gscale(ga(pair(r,dx,yy),pair(r,xx,dy)),F(2)/t),
                        gscale(pair([gs(gscale(dr[i],t),r[i]) for i in range(N)],xx,yy),F(2)/t**2))
            assert pe(pd(full),t)==velocity
            derivative_checks+=1

# Native homogeneous jets, including both imaginary phases and factorials.
jet_checks=0
units=[G(1),G(0,1),G(-1),G(0,-1)]
for m in range(6):
    for n in range(6):
        N=max(m,n)+1
        rho=[{1:G(F(i+1,7)),3:G(F(-(i+1)**3,31)),5:G(F((i+1)**5,1009))} for i in range(N)]
        def jet(order,i):
            w=F((-1)**(order-i)*math.comb(order,i),math.factorial(order)) if i<=order else F(0)
            return {-order:gscale(units[(-order)%4],w)}
        x=[jet(m,i) for i in range(N)];y=[jet(n,i) for i in range(N)]
        E={}
        for i in range(N):
            for j in range(N):
                E=pa(E,pm({-1:G(F(2,i+j+2))},pm(pm(pc(x[i]),y[j]),pa(rho[i],rho[j]))))
        for t in [F(1,7),F(2,17)]:
            r=[pe(p,t) for p in rho];dr=[pe(pd(p),t) for p in rho]
            xx=[pe(p,t) for p in x];yy=[pe(p,t) for p in y]
            readout=[gs(gscale(dr[i],t),gscale(r[i],F(m+n+1))) for i in range(N)]
            assert pe(pd(E),t)==gscale(pair(readout,xx,yy),F(2)/t**2)
            jet_checks+=1

d1=[-1,1,0,0,0,0];d3=[-1,3,-3,1,0,0];d5=[-1,5,-10,10,-5,1]
stencil=0
for u,v in [(F(0),F(0)),(F(-1),F(2)),(F(-1,100),F(1,100000)),(F(2,5),F(-3,7))]:
    w=[{0:G(d5[i]),2:G(-20*u*d3[i]),4:G(120*v*d1[i])} for i in range(6)]
    targets=[{}, {0:v*v}, {0:2*u*v,2:-5*v*v},
        {0:u*u+2*v,2:-84*u*v,4:21*v*v},
        {0:2*u,2:-30*(u*u+14*v),4:1974*u*v,6:-85*v*v},
        {0:F(1),2:-242*u,4:627*u*u+32934*v,6:-37928*u*v,8:341*v*v},
        {2:F(-91),4:16016*u,6:-11440*u*u-1824680*v,8:666666*u*v,10:-1365*v*v}]
    for n in range(7):
        p={};m=2*n+1
        for i in range(6):
            for j in range(6):
                c=F((-1)**n*((i+1)**m+(j+1)**m),14400*(i+j+2))
                p=pa(p,pm(pm(w[i],w[j]),{m-11:G(c)}));stencil+=1
        assert p=={k:G(x) for k,x in targets[n].items() if x},(u,v,n,p,targets[n])

with localcontext() as ctx:
    ctx.prec=160
    h=[D(r['canonical_h']) for r in csv.DictReader(checkpoint.open())]
    delta=h[1]*h[3]-h[2]**2
    u=(h[2]*h[3]-h[1]*h[4])/delta;v=(h[2]*h[4]-h[3]**2)/delta
    limit=2*(h[5]+2*u*h[4]+(u*u+2*v)*h[3]+2*u*v*h[2]+v*v*h[1])
    correction=-10*v*v*h[2]-168*u*v*h[3]-60*(u*u+14*v)*h[4]-484*u*h[5]-182*h[6]
    assert delta>0 and correction>0
    assert abs(h[1]*v+h[2]*u+h[3])<D('1e-160')
    assert abs(h[2]*v+h[3]*u+h[4])<D('1e-160')
    samples=[]
    for den in [20,50,100,200]:
        t=1/D(den);w=[D(d5[i])-20*u*t*t*D(d3[i])+120*v*t**4*D(d1[i]) for i in range(6)]
        g=[sum(2*D((-1)**n)*hn*((i+1)*t)**(2*n+1) for n,hn in enumerate(h)) for i in range(6)]
        incident=sum(w[i]*w[j]*(g[i]+1)*(g[j]+1)/D(i+j+2) for i in range(6) for j in range(6))/(28800*t**11)
        returned=sum(w[i]*w[j]*(g[i]-1)*(g[j]-1)/D(i+j+2) for i in range(6) for j in range(6))/(28800*t**11)
        readout=sum(w[i]*w[j]*(g[i]+g[j])/D(i+j+2) for i in range(6) for j in range(6))/(14400*t**11)
        balance=incident-returned
        assert abs(balance-readout)<D('1e-120') and balance>limit
        samples.append({'h':str(t),'incident_energy':str(incident),'returned_energy':str(returned),
                        'balance':str(balance),'normalized_correction':str((balance-limit)/t**2)})
    record={'PASS':True,'exact_complete_channel_polynomials':whole_checks,
        'exact_material_derivative_checks':derivative_checks,'exact_jet_variation_checks':jet_checks,'exact_six_stencil_contributions':stencil,
        'checkpoint':str(checkpoint),'checkpoint_sha256':expected,'input_column':'canonical_h',
        'input_moments':len(h),'decimal_precision':160,'prefix_delta_diagnostic':str(delta),
        'u_diagnostic':str(u),'v_diagnostic':str(v),'limit_diagnostic':str(limit),
        'correction_diagnostic':str(correction),'samples':samples,
        'scope':'Fraction/Gaussian tests are exact algebra controls with independent complex inputs. Decimal tests use an existing canonical prefix without a tail bound; Lean uses the original complete analytic source and certified intervals. No new moments, zeros or heights were computed.'}
    (evidence/'mechanism-probe.json').write_text(json.dumps(record,indent=2)+'\n')
print(f'PASS: {whole_checks} exact full-channel polynomials, {derivative_checks} exact derivative checks, {jet_checks} native jet-variation checks, {stencil} exact six-stencil contributions, 4 canonical diagnostics.')
