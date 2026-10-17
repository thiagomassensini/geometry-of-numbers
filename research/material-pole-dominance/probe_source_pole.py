"""FINITE numerical diagnostic, not an interval certificate or Lean proof.

Read the preserved canonical source coefficients. Locate a zero of their
finite characteristic polynomial; do not supply a zero of zeta as an input.
The infinite-source zero isolation and readout are NOT certified here.
"""
import hashlib
import json
from pathlib import Path
import mpmath as mp

p=Path('/home/thlinux/momentos/native_jet_exploration/auditoria_corrected_vs_canonical/stage_B/coefficients.json')
r=json.loads(p.read_text())
mp.mp.dps=240
c=list(map(mp.mpf,r['normalized_completed_c']))
h=list(map(mp.mpf,r['canonical_h']))
root=mp.findroot(lambda t: mp.polyval(c[::-1],t),(mp.mpf(198),mp.mpf(202)))
a=1/root
rows=[]
for n in range(1,len(h)):
    e=h[n]-a**(n+1)
    budget=mp.mpf(3)/5*a**(n+1)*(mp.mpf(51)/100)**(n-1)
    C=h[n] if n%2 else h[n]-h[n//2]**2/h[0]
    rows.append({'n':n,'tail_budget_ratio':mp.nstr(abs(e)/budget,30),
                 'C_over_a_power':mp.nstr(C/a**(n+1),30)})
mx=max(rows,key=lambda x:mp.mpf(x['tail_budget_ratio']))
mn=min(rows,key=lambda x:mp.mpf(x['C_over_a_power']))
out={'status':'FINITE_NONRIGOROUS_DIAGNOSTIC','input':str(p),
     'input_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
     'mpmath_dps':mp.mp.dps,'polynomial_degree':len(c)-1,
     'range':'1 <= n <= '+str(len(h)-1),
     'root_squared_height_of_finite_polynomial':mp.nstr(root,60),
     'finite_polynomial_anchor_a':mp.nstr(a,60),
     'max_tail_budget_ratio':mx,'min_normalized_C':mn,
     'rows':rows,'not_certified':['root of infinite source','zero simplicity or completeness',
       'uniform bound for n beyond the finite input','source pole expansion','infinite hierarchy positivity']}
print(json.dumps(out,indent=2))
