#!/usr/bin/env python3
"""Diagnostic only: original completed F, two source channels, native C2 eta.
No zero/height data, moment input, Cholesky, theta quadrature or fitted metric.
Uses the downstream xi identity to evaluate F, not a fresh material synthesis.
"""
from pathlib import Path
import json,platform
import mpmath as mp
root=Path(__file__).resolve().parent

def characteristic(z):
    s=mp.mpf('0.5')+1j*z
    return mp.mpf('0.5')*s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)

def response(z):return -mp.diff(characteristic,z)/(2*characteristic(z))

def run(dps):
    mp.mp.dps=dps
    eta=1/mp.sqrt(2)
    h0=-mp.diff(characteristic,0,2)/(2*characteristic(0))
    J=mp.quad(lambda t:t*t*eta*(2-eta*t)/(1-eta*t)**2,[0,1])
    Jclosed=(1/(1-eta)+mp.log(1-eta)-1)/eta**2-mp.mpf('0.5')
    records=[]
    for kappa in [10,100,1000]:
        z0=mp.j/mp.mpf(kappa);z1=2*mp.j/mp.mpf(kappa)
        r0=response(z0);r1=response(z1)
        ap=mp.sqrt(2)*r0+1j/mp.sqrt(2)
        am=mp.sqrt(2)*r0-1j/mp.sqrt(2)
        delta=mp.sqrt(2)*(r1-r0)
        def R(t):return mp.sqrt(kappa)*delta*eta*(2-eta*t)/(1-eta*t)**2*mp.sqrt(t)*t
        def Bp(t):return mp.sqrt(kappa)*ap*mp.sqrt(t)-R(t)
        def Bm(t):return mp.sqrt(kappa)*am*mp.sqrt(t)-R(t)
        BB=mp.quad(lambda t:(abs(Bp(t))**2-abs(Bm(t))**2)/2,[0,1])
        BR=mp.quad(lambda t:(mp.conj(Bp(t))*R(t)-mp.conj(Bm(t))*R(t))/2,[0,1])
        RB=mp.conj(BR);RR=mp.mpf(0)
        total=r0/z0
        error=abs(BB+BR+RB+RR-total)
        assert BB<0 and BR.real>0 and total.real>0
        assert error<mp.mpf(10)**(-dps+8)
        fmt=lambda v:mp.nstr(v,45)
        records.append({'kappa':kappa,'BB':fmt(BB),'BR_real':fmt(BR.real),
          'RB_real':fmt(RB.real),'RR':'0 (equal-leg identity)',
          'total_native_kernel':fmt(total.real),'reconstruction_error':fmt(error),
          'BB_over_h0':fmt(BB/h0),'BR_over_h0':fmt(BR.real/h0)})
    return {'dps':dps,'eta':mp.nstr(eta,45),'h0_diagnostic':mp.nstr(h0,45),
      'J_integral':mp.nstr(J,45),'J_closed_form_error':mp.nstr(abs(J-Jclosed),8),
      'predicted_BB_over_h0_limit':mp.nstr(1-2*J,45),'rows':records}

results=[run(80),run(120)]
mp.mp.dps=60
for low,high in zip(results[0]['rows'],results[1]['rows']):
    for name in ['BB','BR_real','total_native_kernel']:
        assert abs(mp.mpf(low[name])-mp.mpf(high[name]))<mp.mpf('1e-40')
report={'status':'NUMERICAL_DIAGNOSTIC_NOT_A_LEAN_SIGN_CERTIFICATE',
'python':platform.python_version(),'mpmath':mp.__version__,'source':'NativeScalarZetaIdentification.completedNativeOperatorCharacteristic_eq_completedRiemannZeta',
'inputs':'F and its derivatives only; no moment, zero, height or theta tables',
'native_material_synthesis_reexecuted':False,'results':results}
(root/'evidence/green-sector-diagnostic.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: 80/120 digits; native two-channel Green profiles agree with the total kernel; BB negative, mixed positive.')
print('Predicted normalized bulk limit:',results[1]['predicted_BB_over_h0_limit'])
