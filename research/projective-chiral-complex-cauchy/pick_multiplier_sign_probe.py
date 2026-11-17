#!/usr/bin/env python3
"""C2 physical source Pick/HB multiplier numerical canary, not a Lean proof.
Uses C2 *centered second-difference* Hurwitz continuation, not native as definition.
"""
import mpmath as mp
import json
from pathlib import Path
mp.mp.dps = 90
I = mp.j
def F(z):
    s=mp.mpf('.5')+I*z
    bracket=1+mp.power(4,-s)*(mp.zeta(s,mp.mpf(3)/4)-2*mp.zeta(s,1)+mp.zeta(s,mp.mpf(5)/4))
    camera=(1+mp.power(2,-s))*(1-mp.power(2,1-s))
    A=(s*(s-1)/2)*mp.power(mp.pi,-s/2)*mp.gamma(s/2)
    return A*bracket/camera
def R(z):return -mp.diff(F,z)/(2*F(z))
def Q(z):
    psi=-mp.diff(F,z)
    return (psi-I*F(z))/(psi+I*F(z))
def A(z):
    psi=-mp.diff(F,z)
    return (psi+I*F(z))/(2*F(z))
def K(z,w):return (R(w)-mp.conj(R(z)))/(w-mp.conj(z))
def C(z,w):return I/(w-mp.conj(z))
cases={
    "imaginary_three": [I*mp.mpf(x) for x in ['.05','.10','.20']],
    "offset_four": [mp.mpf(a)+I*mp.mpf(b) for a,b in
        [('.01','.05'),('.08','.12'),('.19','.04'),('.29','.21')]],
    "imaginary_five": [I*mp.mpf(x) for x in ['.035','.065','.10','.14','.195']],
    "offset_six": [mp.mpf(a)+I*mp.mpf(b) for a,b in
        [('0.00','.04'),('.03','.07'),('.11','.12'),('.18','.16'),('.23','.06'),('.32','.21')]]
}
out=[]
for name,zs in cases.items():
    n=len(zs)
    pick=mp.matrix([[K(z,w) for w in zs] for z in zs])
    base=mp.matrix([[C(z,w) for w in zs] for z in zs])
    defect=mp.matrix([[C(z,w)*(1-mp.conj(Q(z))*Q(w)) for w in zs] for z in zs])
    gauges=[A(z) for z in zs]
    gauged=mp.matrix([[mp.conj(gauges[i])*gauges[j]*defect[i,j] for j in range(n)] for i in range(n)])
    min_pick=mp.eighe(pick,eigvals_only=True)[0]
    min_defect=mp.eighe(defect,eigvals_only=True)[0]
    out.append({
        "sample":name,
        "n":n,
        "min_pick_eigenvalue":mp.nstr(min_pick,25),
        "min_defect_eigenvalue":mp.nstr(min_defect,25),
        "max_gram_gauge_error":mp.nstr(max(abs(pick[i,j]-gauged[i,j]) for i in range(n) for j in range(n)),10),
        "max_q_abs":mp.nstr(max(abs(Q(z)) for z in zs),20),
        "max_hermitian_error":mp.nstr(max(abs(pick[i,j]-mp.conj(pick[j,i])) for i in range(n) for j in range(n)),10)
    })
print(json.dumps(out,indent=2))
Path(__file__).with_suffix(".json").write_text(json.dumps(out,indent=2)+"\n")
