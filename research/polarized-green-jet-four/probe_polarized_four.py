#!/usr/bin/env python3
"""Independent finite diagnostic of the original completed F and physical
Cauchy source. No zero/height/moment tables; no material TFVD resynthesis.
"""
from pathlib import Path
import json,platform
import mpmath as mp
root=Path(__file__).resolve().parent

def F(z):
    s=mp.mpf('.5')+mp.j*z
    # Gamma(1+s/2)=(s/2)Gamma(s/2) removes the artificial pole at s=0.
    return (s-1)*mp.power(mp.pi,-s/2)*mp.gamma(1+s/2)*mp.zeta(s)

def response(z):return -mp.diff(F,z)/(2*F(z))

def run(dps):
    mp.mp.dps=dps
    # Coefficients of R from 2 F R = -F', avoiding nested high derivatives.
    f=mp.taylor(F,0,14)
    r=[]
    for n in range(14):r.append((-(n+1)*f[n+1]/2-sum(f[j]*r[n-j] for j in range(1,n+1)))/f[0])
    h=[r[2*n+1].real for n in range(7)]
    assert max(abs(f[2*n+1]) for n in range(7))<mp.mpf(10)**(-dps+10)
    A=mp.matrix([[h[0],h[1]],[h[1],h[2]]]);b=mp.matrix([h[2],h[3]])
    invc=mp.lu_solve(A,b)
    critical=[-invc[0],-invc[1],mp.mpf(1)]
    pairs=[('critical',critical,critical),('independent',[mp.mpf(1),mp.mpf(-2),mp.mpf(3)],
            [mp.mpf(-1),mp.mpf(4),mp.mpf('.5')])]
    cm=mp.matrix([[-h[1],-20*h[2],-126*h[3]],[-20*h[2],-14*h[3],-75*h[4]],[-126*h[3],-75*h[4],-55*h[5]]])
    qm=mp.matrix([[h[2],231*h[3],6027*h[4]],[231*h[3],147*h[4],3102*h[5]],[6027*h[4],3102*h[5],2002*h[6]]])
    pairing=lambda M,u,v:sum(u[i]*v[j]*M[i,j] for i in range(3) for j in range(3))
    eta=1/mp.sqrt(2)
    phi=lambda j,x:mp.sqrt(x)*x**j
    gc=lambda j,x:phi(j,x)/(1-eta*x)**2
    P=lambda x:eta*(2-eta*x)*phi(1,x)/(1-eta*x)**2
    Q=lambda x:-eta**2*gc(3,x)
    fmt=lambda x:mp.nstr(x,45)
    rows=[]
    for K in [10,100,1000]:
        values=[response(mp.j*(j+1)/K) for j in range(6)]
        inc=[values[j+1]-values[j] for j in range(5)]
        alpha=mp.sqrt(2*K)
        def vf(j,x):
            if j==0:return inc[0]*P(x)
            if j==1:return inc[1]*Q(x)
            return inc[j-1]*gc(j,x)-eta**2*inc[j]*gc(j+2,x)
        S=lambda j,leg,x:alpha*(values[j]+(1 if leg==0 else -1)*mp.j/2)*phi(j,x)
        E=lambda j,x:alpha*vf(j,x)
        B=lambda j,leg,x:S(j,leg,x)-E(j,x)
        mixed=[]
        for i in range(5):
            row=[]
            for j in range(5):
                exact=-mp.j*K*mp.quad(lambda x:phi(i,x)*vf(j,x),[0,1])
                physical=mp.quad(lambda x:(mp.conj(B(i,0,x))*E(j,x)-mp.conj(B(i,1,x))*E(j,x))/2,[0,1])
                assert abs(physical-exact)<mp.mpf(10)**(-dps+12)
                row.append(physical)
            mixed.append(row)
        def weights(u):
            t=mp.mpf(K)
            return [u[0]-u[1]*t**2/2+u[2]*t**4/24,u[1]*t**2-u[2]*t**4/6,
                    -u[1]*t**2/2+u[2]*t**4/4,-u[2]*t**4/6,u[2]*t**4/24]
        for label,u,v in pairs:
            wu,wv=weights(u),weights(v)
            Bs=lambda w,leg,x:sum(w[j]*B(j,leg,x) for j in range(5))
            Es=lambda w,x:sum(w[j]*E(j,x) for j in range(5))
            Ss=lambda w,leg,x:sum(w[j]*S(j,leg,x) for j in range(5))
            BB=mp.quad(lambda x:(mp.conj(Bs(wu,0,x))*Bs(wv,0,x)-mp.conj(Bs(wu,1,x))*Bs(wv,1,x))/2,[0,1])
            BE=sum(wu[i]*wv[j]*mixed[i][j] for i in range(5) for j in range(5))
            EB=mp.conj(sum(wv[i]*wu[j]*mixed[i][j] for i in range(5) for j in range(5)))
            total=mp.quad(lambda x:(mp.conj(Ss(wu,0,x))*Ss(wv,0,x)-mp.conj(Ss(wu,1,x))*Ss(wv,1,x))/2,[0,1])
            basis=sum(wu[i]*wv[j]*K*(values[i].imag+values[j].imag)/mp.mpf(i+j+2) for i in range(5) for j in range(5))
            assert abs(BB+BE+EB-total)<mp.mpf(10)**(-dps+32)
            assert abs(basis-total)<mp.mpf(10)**(-dps+32)
            finite=sum(u[i]*v[j]*h[i+j] for i in range(3) for j in range(3))
            corr=pairing(cm,u,v);fourth=pairing(qm,u,v)
            rows.append({'label':label,'kappa':K,'BB':fmt(BB.real),'BE':fmt(BE.real),'EB':fmt(EB.real),
             'total':fmt(total.real),'finite_term':fmt(finite),'correction':fmt(corr),'fourth':fmt(fourth),
             'reconstruction_error':fmt(abs(BB+BE+EB-total)),
             'scaled_first':fmt(K**2*(total.real-finite)),
             'scaled_fourth':fmt(K**4*(total.real-finite-corr/K**2)),
             'scaled_sixth_error':fmt(K**6*(total.real-finite-corr/K**2-fourth/K**4)),
             'ordered_mixed_real':[[fmt(z.real) for z in row] for row in mixed]})
    return {'dps':dps,'original_moments_diagnostic':[fmt(z) for z in h],
      'inverse_coefficients':[fmt(z) for z in invc],
      'critical_old_pairings':[fmt(sum(critical[i]*h[i+j] for i in range(3))) for j in range(2)],'rows':rows}

results=[run(80),run(120)]
mp.mp.dps=60
for lo,hi in zip(results[0]['rows'],results[1]['rows']):
    for key in ['total','scaled_first','scaled_fourth','scaled_sixth_error']:
        assert abs(mp.mpf(lo[key])-mp.mpf(hi[key]))<mp.mpf('1e-26'),(key,lo,hi)
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/polarized-four-diagnostic.json').write_text(json.dumps({
 'status':'NUMERICAL_DIAGNOSTIC_NOT_A_PROOF','material_synthesis_reexecuted':False,
 'python':platform.python_version(),'mpmath':mp.__version__,
 'provenance':'NativeScalarZetaIdentification.completedNativeOperatorCharacteristic_eq_completedRiemannZeta',
 'inputs':'original F and Taylor recurrence only; no zero/height/moment tables','results':results},indent=2)+'\n')
print('PASS: 80/120 digits, 25 ordered crosses, independent arguments, original Green balance.')
for row in results[-1]['rows']:
    if row['label']=='critical' and row['kappa']==1000:
        print('Critical finite term:',row['finite_term'])
        print('Critical correction:',row['correction'])
        print('Critical fourth:',row['fourth'])
