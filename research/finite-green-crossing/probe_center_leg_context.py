#!/usr/bin/env python3
"""Independent scalar checks of user center/legs notes; not Lean evidence."""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=80
root=Path(__file__).resolve().parent
rows=[]
for c,r in [(mp.mpf(4),mp.mpf(1)),(mp.mpf(8),mp.mpf(2)),(mp.mpf(8),mp.mpf(1))]:
    g=mp.sqrt(c*c-r*r)
    q=mp.sqrt((c+r)/(c-r))
    alpha=mp.log(q);beta=mp.log(c/g)
    for t in [mp.mpf(0),mp.mpf(3),mp.mpf(14)]:
        s=mp.mpf('0.5')+mp.j*t
        wave=lambda n:mp.exp(-s*mp.log(n))
        original=wave(c-r)-2*wave(c)+wave(c+r)
        reciprocal=mp.exp(-s*mp.log(g))*(mp.exp(s*alpha/2)-mp.exp(-s*alpha/2))**2
        center=2*(mp.exp(-s*mp.log(g))-wave(c))
        closed=2*wave(c)*(mp.exp(s*beta)*mp.cosh(s*alpha)-1)
        doubled=wave(2*(c-r))-2*wave(2*c)+wave(2*(c+r))
        assert abs(original-reciprocal-center)<mp.mpf('1e-75')
        assert abs(original-closed)<mp.mpf('1e-75')
        assert abs(abs(doubled)**2-abs(original)**2/2)<mp.mpf('1e-75')
        # Full vector energy-curvature identity in the original two real quadratures.
        u,v,w=wave(c-r),wave(c),wave(c+r)
        lhs=-mp.re(mp.conj(v)*(u-2*v+w))
        rhs=(abs(u-v)**2+abs(w-v)**2)/2-(abs(u)**2-2*abs(v)**2+abs(w)**2)/2
        assert abs(lhs-rhs)<mp.mpf('1e-75')
        rows.append({'center':str(c),'radius':str(r),'t':str(t),'reciprocal':mp.nstr(reciprocal,28),
          'center_correction':mp.nstr(center,28),'bracket':mp.nstr(original,28),
          'energy':mp.nstr(abs(original)**2,28),'signed_energy_curvature_balance':mp.nstr(lhs,28)})
assert mp.mpf(rows[0]['signed_energy_curvature_balance'])<0
(root/'evidence/center-leg-context-diagnostic.json').write_text(json.dumps({'dps':80,'cases':rows,
  'scope':'Scalar note identities only; geometric deformation q is not the Green weight eta; fixed-radius motion is not full dilation; no canonical Hankel sign follows.'},indent=2)+'\n')
print('PASS 9 complex-parameter cases; reciprocal plus center correction, full dilation and energy curvature balance; negative real counterexample retained.')
