#!/usr/bin/env python3
"""Independent C2 bracket vs completed native zeta, on COMPLEX heights.

Source genealogy: genuine C2 seed + (4k+3,4k+4,4k+5) centered differences,
then the exact base-two camera factor and archimedean completion. The
comparison with A(z)*zeta(s) is a reference check, not an initial definition.

Hurwitz analytic continuation of the C2 *second-difference* series is
absolutely convergent in its initial half-plane, and its exact Hurwitz
expression continues it to the tested points.
"""
from pathlib import Path
import mpmath as m
import json
m.mp.dps=95
I=m.j
def s(z):
    return m.mpf('0.5')+I*z
def q2(z):
    x=s(z)
    return (1+m.power(2,-x))*(1-m.power(2,1-x))
def c2_chart(z):
    x=s(z)
    return 1+m.power(4,-x)*(m.zeta(x,m.mpf(3)/4)-2*m.zeta(x,1)+m.zeta(x,m.mpf(5)/4))
def arch(z):
    x=s(z)
    return m.mpf('.5')*x*(x-1)*m.power(m.pi,-x/2)*m.gamma(x/2)
def fc2(z):
    return arch(z)*c2_chart(z)/q2(z)
def fnative(z):
    return arch(z)*m.zeta(s(z))
def R(f,z):
    return -m.diff(f,z)/(2*f(z))
def K(f,z,w):
    return (R(f,w)-m.conj(R(f,z)))/(w-m.conj(z))
def c2_partial(z,n):
    x=s(z)
    return 1+sum(m.power(4*k+3,-x)-2*m.power(4*k+4,-x)+m.power(4*k+5,-x) for k in range(n))
heights=[I*m.mpf('0.05'), I*m.mpf('0.10'), I*m.mpf('0.20'), m.mpf('0.1')+I*m.mpf('0.07')]
report={"dps":m.mp.dps,
        "meaning":"independent exact C2 Hurwitz second-difference analytic continuation compared with native reference",
        "heights":[], "samples":[]}
for z in heights:
    diff=fc2(z)-fnative(z)
    rd=R(fc2,z)-R(fnative,z)
    report["heights"].append({"z":m.nstr(z,16),"abs_completed_diff":m.nstr(abs(diff),20),
      "abs_normalized_response_diff":m.nstr(abs(rd),20),
      "abs_c2_chart_minus_camera_times_zeta":m.nstr(abs(c2_chart(z)-q2(z)*m.zeta(s(z))),20)})
for n in (100,1000,4000):
    z=heights[1]
    report["samples"].append({"partial_cells":n,
      "absolute_bracket_tail_at_z_0_10i":m.nstr(abs(c2_partial(z,n)-c2_chart(z)),20)})
H=heights[:3]
Kc=m.matrix(3);Kn=m.matrix(3)
for a,z in enumerate(H):
    for b,w in enumerate(H):
        Kc[a,b]=K(fc2,z,w); Kn[a,b]=K(fnative,z,w)
evals=m.eighe(Kc,eigvals_only=True)
def hb_gauge(f,z):
    F=f(z); Psi=-m.diff(f,z)
    return (Psi+I*F)/(2*F)
def hb_quotient(f,z):
    F=f(z); Psi=-m.diff(f,z)
    return (Psi-I*F)/(Psi+I*F)
def K_hb(f,z,w):
    return (I/(w-m.conj(z)) * m.conj(hb_gauge(f,z)) * hb_gauge(f,w) *
            (1-m.conj(hb_quotient(f,z))*hb_quotient(f,w)))
hb_error=max(abs(K(fc2,H[i],H[j])-K_hb(fc2,H[i],H[j]))
             for i in range(3) for j in range(3))
report["pick"]={"n":3,
                "max_entrywise_difference":m.nstr(max(abs(Kc[i,j]-Kn[i,j]) for i in range(3) for j in range(3)),20),
                "max_physical_HB_factorization_error":m.nstr(hb_error,20),
                "min_eigenvalue":m.nstr(evals[0],22),
                "max_eigenvalue":m.nstr(evals[2],22),
                "status":"numerical non-interval only, not a sign proof"}
out=json.dumps(report,indent=2)
print(out)
Path(__file__).with_name("numerical-c2-vs-native.json").write_text(out+"\n")
