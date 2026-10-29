#!/usr/bin/env python3
"""Finite diagnostic only. Uses the proved downstream xi identity to evaluate
the original completed characteristic, not a new material synthesis. No zeros,
heights, moment tables, Cholesky or theta quadrature are supplied as inputs.
"""
from pathlib import Path
import json
import platform
import mpmath as mp

root=Path(__file__).resolve().parent

def characteristic(z):
    s=mp.mpf('0.5')+mp.j*z
    return s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)/2

def response(z):
    return -mp.diff(characteristic,z)/(2*characteristic(z))

def run(dps):
    mp.mp.dps=dps
    eta=1/mp.sqrt(2)
    h0=mp.diff(response,0)
    h1=mp.diff(response,0,3)/mp.factorial(3)
    P=lambda x:eta*(2-eta*x)/(1-eta*x)**2*mp.sqrt(x)*x
    Q=lambda x:-eta**2/(1-eta*x)**2*mp.sqrt(x)*x**3
    feature=lambda j,x:mp.sqrt(x)*x**j
    ports=[P,Q]
    overlap=[[mp.quad(lambda x:feature(i,x)*ports[j](x),[0,1]) for j in range(2)] for i in range(2)]
    A=mp.quad(lambda x:eta*x*x*(1-x)*(2-eta*x+eta*x*x)/(1-eta*x)**2,[0,1])
    assert A>=eta/12
    rows=[]
    for kappa in [10,100,1000]:
        delta=mp.j/kappa
        values=[response((j+1)*delta) for j in range(3)]
        increments=[values[j+1]-values[j] for j in range(2)]
        alpha=mp.sqrt(2*kappa)
        S=lambda j,leg,x:alpha*(values[j]+(1 if leg==0 else -1)*mp.j/2)*feature(j,x)
        E=lambda j,x:alpha*increments[j]*ports[j](x)
        B=lambda j,leg,x:S(j,leg,x)-E(j,x)
        crosses=[]
        for i in range(2):
            cr=[]
            for j in range(2):
                integral=mp.quad(lambda x:(mp.conj(B(i,0,x))*E(j,x)-mp.conj(B(i,1,x))*E(j,x))/2,[0,1])
                exact=-mp.j*kappa*increments[j]*overlap[i][j]
                assert abs(integral-exact)<mp.mpf(10)**(-dps+10)
                cr.append(integral)
            crosses.append(cr)
        Ejet=lambda x:(E(1,x)-E(0,x))/delta
        Bjet=lambda leg,x:(B(1,leg,x)-B(0,leg,x))/delta
        BB=mp.quad(lambda x:(abs(Bjet(0,x))**2-abs(Bjet(1,x))**2)/2,[0,1])
        BE=mp.quad(lambda x:(mp.conj(Bjet(0,x))*Ejet(x)-mp.conj(Bjet(1,x))*Ejet(x))/2,[0,1])
        weighted=kappa**2*(crosses[1][1]-crosses[1][0]-crosses[0][1]+crosses[0][0])
        total=2*kappa**3*(values[1].imag/4+values[0].imag/2-(values[1].imag+values[0].imag)/3)
        error=abs(BB+2*BE.real-total)
        assert abs(weighted-BE)<mp.mpf(10)**(-dps+14)
        assert error<mp.mpf(10)**(-dps+15)
        assert BB<0 and BE.real>0 and total>0
        fmt=lambda v:mp.nstr(v,45)
        rows.append({'kappa':kappa,'BB':fmt(BB),'BE_real':fmt(BE.real),'EB_real':fmt(BE.real),
          'EE':'0 (proved equal legs, not a zero vector)',
          'residual_hilbert_norm_squared':fmt(2*mp.quad(lambda x:abs(Ejet(x))**2,[0,1])),
          'total_same_native_kernel':fmt(total),'total_minus_h1':fmt(total-h1.real),
          'reconstruction_error':fmt(error),'BB_over_kappa_squared':fmt(BB/kappa**2),
          'BE_over_kappa_squared':fmt(BE.real/kappa**2),
          'ordered_crosses_real':[[fmt(v.real) for v in row] for row in crosses]})
    return {'dps':dps,'eta':mp.nstr(eta,45),'h0_diagnostic':mp.nstr(h0.real,45),
      'h1_diagnostic':mp.nstr(h1.real,45),'A_integral':mp.nstr(A,45),
      'predicted_BE_scaled_limit':mp.nstr((h0*A).real,45),
      'predicted_BB_scaled_limit':mp.nstr((-2*h0*A).real,45),'rows':rows}

results=[run(80),run(120)]
mp.mp.dps=60
for low,high in zip(results[0]['rows'],results[1]['rows']):
    for name in ['BB','BE_real','total_same_native_kernel','BE_over_kappa_squared']:
        assert abs(mp.mpf(low[name])-mp.mpf(high[name]))<mp.mpf('1e-38')
report={'status':'NUMERICAL_DIAGNOSTIC_NOT_A_PROOF','python':platform.python_version(),
  'mpmath':mp.__version__,'material_synthesis_reexecuted':False,
  'evaluation_provenance':'NativeScalarZetaIdentification.completedNativeOperatorCharacteristic_eq_completedRiemannZeta',
  'inputs':'completed characteristic and derivatives; no zeros, heights or moment data',
  'results':results}
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/first-odd-diagnostic.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: 80/120 digits, four ordered crosses and complete first odd source; quadratic growth diagnostic.')
print('A(C2) =',results[-1]['A_integral'])
print('h1 diagnostic =',results[-1]['h1_diagnostic'])
