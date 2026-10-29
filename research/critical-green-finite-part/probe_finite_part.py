#!/usr/bin/env python3
"""Independent diagnostic; evaluates the original F via its proved downstream
xi identity. No material resynthesis, zero/height inputs, or sign certificate.
"""
from pathlib import Path
import json,platform
import mpmath as mp
root=Path(__file__).resolve().parent
def F(z):
    s=mp.mpf('.5')+mp.j*z
    return s*(s-1)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)/2
def R(z):return -mp.diff(F,z)/(2*F(z))
def run(dps):
    mp.mp.dps=dps
    eta=1/mp.sqrt(2)
    h=[mp.diff(R,0,2*n+1)/mp.factorial(2*n+1) for n in range(5)]
    a=(h[1]/h[0]).real
    pivot=(h[2]-h[1]**2/h[0]).real
    correction=(-a*a*h[1]+40*a*h[2]-14*h[3]).real
    fourth=(a*a*h[2]-462*a*h[3]+147*h[4]).real
    phi=lambda j,x:mp.sqrt(x)*x**j
    gc=lambda j,x:phi(j,x)/(1-eta*x)**2
    P=lambda x:eta*(2-eta*x)*phi(1,x)/(1-eta*x)**2
    Q=lambda x:-eta**2*gc(3,x)
    leading=mp.quad(lambda x:phi(0,x)*(1-x)**2*
      ((1-eta**2)*gc(2,x)+2*eta*gc(1,x)+2*eta**2*gc(3,x)-eta**2*gc(4,x)),[0,1])/4
    rows=[]
    for kappa in [10,100,1000]:
        delta=mp.j/kappa
        values=[R((j+1)*delta) for j in range(4)]
        inc=[values[j+1]-values[j] for j in range(3)]
        alpha=mp.sqrt(2*kappa)
        feat=[lambda x:inc[0]*P(x),lambda x:inc[1]*Q(x),
              lambda x:inc[1]*gc(2,x)-eta**2*inc[2]*gc(4,x)]
        S=lambda j,leg,x:alpha*(values[j]+(1 if leg==0 else -1)*mp.j/2)*phi(j,x)
        E=lambda j,x:alpha*feat[j](x)
        B=lambda j,leg,x:S(j,leg,x)-E(j,x)
        nu=1/(2*delta**2)
        coeff=[nu-a,-2*nu,nu]
        mixed=[]
        for i in range(3):
            row=[]
            for j in range(3):
                exact=-mp.j*kappa*mp.quad(lambda x:phi(i,x)*feat[j](x),[0,1])
                physical=mp.quad(lambda x:(mp.conj(B(i,0,x))*E(j,x)-mp.conj(B(i,1,x))*E(j,x))/2,[0,1])
                assert abs(physical-exact)<mp.mpf(10)**(-dps+10)
                row.append(physical)
            mixed.append(row)
        Ec=lambda x:sum(coeff[j]*E(j,x) for j in range(3))
        Bc=lambda leg,x:sum(coeff[j]*B(j,leg,x) for j in range(3))
        BB=mp.quad(lambda x:(abs(Bc(0,x))**2-abs(Bc(1,x))**2)/2,[0,1])
        BE=mp.quad(lambda x:(mp.conj(Bc(0,x))*Ec(x)-mp.conj(Bc(1,x))*Ec(x))/2,[0,1])
        total=mp.quad(lambda x:(abs(sum(coeff[j]*S(j,0,x) for j in range(3)))**2-
                                    abs(sum(coeff[j]*S(j,1,x) for j in range(3)))**2)/2,[0,1])
        nine=sum(mp.conj(coeff[i])*coeff[j]*mixed[i][j] for i in range(3) for j in range(3))
        sample=kappa*((a*a+mp.mpf(7)*a*kappa**2/12+mp.mpf(kappa)**4/24)*values[0].imag+
          (-mp.mpf(2)*a*kappa**2/3-mp.mpf(kappa)**4/30)*values[1].imag+
          (a*kappa**2/4+mp.mpf(kappa)**4/120)*values[2].imag)
        assert abs(sample-total)<mp.mpf(10)**(-dps+20)
        err=abs(BB+2*BE.real-total)
        assert err<mp.mpf(10)**(-dps+20)
        assert abs(nine-BE)<mp.mpf(10)**(-dps+20)
        fmt=lambda x:mp.nstr(x,45)
        rows.append({'kappa':kappa,'BB':fmt(BB),'BE_real':fmt(BE.real),'total':fmt(total),
          'total_minus_pivot':fmt(total-pivot),
          'scaled_first':fmt(kappa**2*(total-pivot)),
          'scaled_fourth':fmt(kappa**4*(total-pivot-correction/kappa**2)),
          'scaled_sixth_error':fmt(kappa**6*(total-pivot-correction/kappa**2-fourth/kappa**4)),
          'three_sample_formula_error':fmt(abs(sample-total)),'reconstruction_error':fmt(err),
          'BE_over_kappa_four':fmt(BE.real/kappa**4),
          'ordered_mixed_real':[[fmt(z.real) for z in row] for row in mixed]})
    return {'dps':dps,'a':mp.nstr(a,45),'pivot_diagnostic':mp.nstr(pivot,45),
      'leading_coefficient_diagnostic':mp.nstr(leading,45),
      'correction_diagnostic':mp.nstr(correction,45),'fourth_diagnostic':mp.nstr(fourth,45),
      'moments_0_through_4_diagnostic':[mp.nstr(z.real,45) for z in h],
      'predicted_BE_kappa_four_limit_NOT_FORMALIZED':mp.nstr((h[0]*leading).real,45),'rows':rows}
results=[run(80),run(120)]
mp.mp.dps=60
for lo,hi in zip(results[0]['rows'],results[1]['rows']):
    for key in ['BB','BE_real','total','scaled_first','scaled_fourth','scaled_sixth_error']:
        assert abs(mp.mpf(lo[key])-mp.mpf(hi[key]))<mp.mpf('1e-35')
(root/'evidence').mkdir(exist_ok=True)
(root/'evidence/finite-part-diagnostic.json').write_text(json.dumps({
 'status':'NUMERICAL_DIAGNOSTIC_NOT_A_PROOF','material_synthesis_reexecuted':False,
 'python':platform.python_version(),'mpmath':mp.__version__,
 'provenance':'NativeScalarZetaIdentification.completedNativeOperatorCharacteristic_eq_completedRiemannZeta',
 'inputs':'original F and derivatives only; no zero/height/moment tables','results':results},indent=2)+'\n')
print('PASS: 80/120 digits, nine ordered crosses, original critical direction, full balance.')
print('Second even pivot diagnostic:',results[-1]['pivot_diagnostic'])
print('First correction:',results[-1]['correction_diagnostic'])
print('Fourth-order correction:',results[-1]['fourth_diagnostic'])
